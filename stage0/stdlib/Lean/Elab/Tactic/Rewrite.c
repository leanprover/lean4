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
lean_object* l_Lean_indentD(lean_object*);
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
static const lean_string_object l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 300, .m_capacity = 300, .m_length = 299, .m_data = "The target expression is not type-correct under the `instances` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue."};
static const lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__2;
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
static lean_object* _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1, &l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1);
v___x_27_ = l_Lean_MessageData_note(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(lean_object* v_e_28_, uint8_t v___x_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_check(v_e_28_, v___x_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_35_, 0);
lean_dec(v_unused_44_);
v___x_37_ = v___x_35_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_dec(v___x_35_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_39_ = l_Lean_MessageData_nil;
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_60_; 
v_a_45_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_60_ == 0)
{
v___x_47_ = v___x_35_;
v_isShared_48_ = v_isSharedCheck_60_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_35_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_60_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
uint8_t v___y_50_; uint8_t v___x_58_; 
v___x_58_ = l_Lean_Exception_isInterrupt(v_a_45_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
lean_inc(v_a_45_);
v___x_59_ = l_Lean_Exception_isRuntime(v_a_45_);
v___y_50_ = v___x_59_;
goto v___jp_49_;
}
else
{
v___y_50_ = v___x_58_;
goto v___jp_49_;
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_53_; 
lean_dec(v_a_45_);
v___x_51_ = lean_obj_once(&l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__2, &l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__2);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 0);
lean_ctor_set(v___x_47_, 0, v___x_51_);
v___x_53_ = v___x_47_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
else
{
lean_object* v___x_56_; 
if (v_isShared_48_ == 0)
{
v___x_56_ = v___x_47_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_45_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed(lean_object* v_e_61_, lean_object* v___x_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
uint8_t v___x_12849__boxed_68_; lean_object* v_res_69_; 
v___x_12849__boxed_68_ = lean_unbox(v___x_62_);
v_res_69_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_61_, v___x_12849__boxed_68_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2(lean_object* v_typeCheckNote_70_, lean_object* v_x_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_72_, 0, v_x_71_);
lean_ctor_set(v___x_72_, 1, v_typeCheckNote_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(lean_object* v_e_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___f_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_typeCheckNote_91_; lean_object* v___f_92_; lean_object* v___x_93_; 
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
lean_inc(v___y_76_);
lean_inc_ref(v___y_75_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_84_, 0, v_x_74_);
lean_closure_set(v___f_84_, 1, v___y_75_);
lean_closure_set(v___f_84_, 2, v___y_76_);
lean_closure_set(v___f_84_, 3, v___y_77_);
lean_closure_set(v___f_84_, 4, v___y_78_);
v___x_85_ = 3;
v___x_86_ = lean_box(v___x_85_);
lean_inc_ref(v_e_73_);
v___f_87_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed), 7, 2);
lean_closure_set(v___f_87_, 0, v_e_73_);
lean_closure_set(v___f_87_, 1, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_mk_empty_array_with_capacity(v___x_88_);
v___x_90_ = lean_array_push(v___x_89_, v_e_73_);
v_typeCheckNote_91_ = l_Lean_MessageData_ofLazyM(v___f_87_, v___x_90_);
v___f_92_ = lean_alloc_closure((void*)(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2), 2, 1);
lean_closure_set(v___f_92_, 0, v_typeCheckNote_91_);
v___x_93_ = l_Lean_Meta_mapErrorImp___redArg(v___f_84_, v___f_92_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_93_) == 0)
{
return v___x_93_;
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___boxed(lean_object* v_e_102_, lean_object* v_x_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_102_, v_x_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(lean_object* v_00_u03b1_114_, lean_object* v_e_115_, lean_object* v_x_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_115_, v_x_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(lean_object* v_00_u03b1_127_, lean_object* v_e_128_, lean_object* v_x_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(v_00_u03b1_127_, v_e_128_, v_x_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_Elab_abortTacticExceptionId;
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___boxed(lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(lean_object* v_00_u03b1_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___boxed(lean_object* v_00_u03b1_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(v_00_u03b1_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0(lean_object* v_mvarId_170_, lean_object* v_e_171_, lean_object* v_a_172_, uint8_t v_symm_173_, lean_object* v_config_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_MVarId_rewrite(v_mvarId_170_, v_e_171_, v_a_172_, v_symm_173_, v_config_174_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed(lean_object* v_mvarId_185_, lean_object* v_e_186_, lean_object* v_a_187_, lean_object* v_symm_188_, lean_object* v_config_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_symm_boxed_199_; lean_object* v_res_200_; 
v_symm_boxed_199_ = lean_unbox(v_symm_188_);
v_res_200_ = l_Lean_Elab_Tactic_elabRewrite___lam__0(v_mvarId_185_, v_e_186_, v_a_187_, v_symm_boxed_199_, v_config_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_200_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
else
{
lean_object* v_key_204_; lean_object* v_tail_205_; uint8_t v___x_206_; 
v_key_204_ = lean_ctor_get(v_x_202_, 0);
v_tail_205_ = lean_ctor_get(v_x_202_, 2);
v___x_206_ = lean_expr_eqv(v_key_204_, v_a_201_);
if (v___x_206_ == 0)
{
v_x_202_ = v_tail_205_;
goto _start;
}
else
{
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_208_, lean_object* v_x_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_208_, v_x_209_);
lean_dec(v_x_209_);
lean_dec_ref(v_a_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(lean_object* v_m_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_buckets_214_; lean_object* v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v_fold_219_; uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_buckets_214_ = lean_ctor_get(v_m_212_, 1);
v___x_215_ = lean_array_get_size(v_buckets_214_);
v___x_216_ = l_Lean_Expr_hash(v_a_213_);
v___x_217_ = 32ULL;
v___x_218_ = lean_uint64_shift_right(v___x_216_, v___x_217_);
v_fold_219_ = lean_uint64_xor(v___x_216_, v___x_218_);
v___x_220_ = 16ULL;
v___x_221_ = lean_uint64_shift_right(v_fold_219_, v___x_220_);
v___x_222_ = lean_uint64_xor(v_fold_219_, v___x_221_);
v___x_223_ = lean_uint64_to_usize(v___x_222_);
v___x_224_ = lean_usize_of_nat(v___x_215_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_sub(v___x_224_, v___x_225_);
v___x_227_ = lean_usize_land(v___x_223_, v___x_226_);
v___x_228_ = lean_array_uget_borrowed(v_buckets_214_, v___x_227_);
v___x_229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_213_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_230_, lean_object* v_a_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_230_, v_a_231_);
lean_dec_ref(v_a_231_);
lean_dec_ref(v_m_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(lean_object* v_mvarId_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; lean_object* v_mctx_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_238_ = lean_st_ref_get(v___y_236_);
v_mctx_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_mctx_239_);
lean_dec(v___x_238_);
v___x_240_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_239_, v_mvarId_234_);
lean_dec_ref(v_mctx_239_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___y_235_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_mvarId_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec(v_mvarId_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(lean_object* v_mvarId_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; lean_object* v_mctx_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_253_ = lean_st_ref_get(v___y_251_);
v_mctx_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_mctx_254_);
lean_dec(v___x_253_);
v___x_255_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_254_, v_mvarId_249_);
lean_dec_ref(v_mctx_254_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___y_250_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg___boxed(lean_object* v_mvarId_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec(v_mvarId_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
return v_x_264_;
}
else
{
lean_object* v_key_266_; lean_object* v_value_267_; lean_object* v_tail_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_291_; 
v_key_266_ = lean_ctor_get(v_x_265_, 0);
v_value_267_ = lean_ctor_get(v_x_265_, 1);
v_tail_268_ = lean_ctor_get(v_x_265_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_291_ == 0)
{
v___x_270_ = v_x_265_;
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_tail_268_);
lean_inc(v_value_267_);
lean_inc(v_key_266_);
lean_dec(v_x_265_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v_fold_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_272_ = lean_array_get_size(v_x_264_);
v___x_273_ = l_Lean_Expr_hash(v_key_266_);
v___x_274_ = 32ULL;
v___x_275_ = lean_uint64_shift_right(v___x_273_, v___x_274_);
v_fold_276_ = lean_uint64_xor(v___x_273_, v___x_275_);
v___x_277_ = 16ULL;
v___x_278_ = lean_uint64_shift_right(v_fold_276_, v___x_277_);
v___x_279_ = lean_uint64_xor(v_fold_276_, v___x_278_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = lean_usize_of_nat(v___x_272_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_sub(v___x_281_, v___x_282_);
v___x_284_ = lean_usize_land(v___x_280_, v___x_283_);
v___x_285_ = lean_array_uget_borrowed(v_x_264_, v___x_284_);
lean_inc(v___x_285_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 2, v___x_285_);
v___x_287_ = v___x_270_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_key_266_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_value_267_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_285_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_array_uset(v_x_264_, v___x_284_, v___x_287_);
v_x_264_ = v___x_288_;
v_x_265_ = v_tail_268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(lean_object* v_i_292_, lean_object* v_source_293_, lean_object* v_target_294_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_array_get_size(v_source_293_);
v___x_296_ = lean_nat_dec_lt(v_i_292_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v_source_293_);
lean_dec(v_i_292_);
return v_target_294_;
}
else
{
lean_object* v_es_297_; lean_object* v___x_298_; lean_object* v_source_299_; lean_object* v_target_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_es_297_ = lean_array_fget(v_source_293_, v_i_292_);
v___x_298_ = lean_box(0);
v_source_299_ = lean_array_fset(v_source_293_, v_i_292_, v___x_298_);
v_target_300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_target_294_, v_es_297_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_292_, v___x_301_);
lean_dec(v_i_292_);
v_i_292_ = v___x_302_;
v_source_293_ = v_source_299_;
v_target_294_ = v_target_300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object* v_data_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_nbuckets_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_305_ = lean_array_get_size(v_data_304_);
v___x_306_ = lean_unsigned_to_nat(2u);
v_nbuckets_307_ = lean_nat_mul(v___x_305_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_box(0);
v___x_310_ = lean_mk_array(v_nbuckets_307_, v___x_309_);
v___x_311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v___x_308_, v_data_304_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(lean_object* v_m_312_, lean_object* v_a_313_, lean_object* v_b_314_){
_start:
{
lean_object* v_size_315_; lean_object* v_buckets_316_; lean_object* v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v_fold_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; lean_object* v_bkt_330_; uint8_t v___x_331_; 
v_size_315_ = lean_ctor_get(v_m_312_, 0);
v_buckets_316_ = lean_ctor_get(v_m_312_, 1);
v___x_317_ = lean_array_get_size(v_buckets_316_);
v___x_318_ = l_Lean_Expr_hash(v_a_313_);
v___x_319_ = 32ULL;
v___x_320_ = lean_uint64_shift_right(v___x_318_, v___x_319_);
v_fold_321_ = lean_uint64_xor(v___x_318_, v___x_320_);
v___x_322_ = 16ULL;
v___x_323_ = lean_uint64_shift_right(v_fold_321_, v___x_322_);
v___x_324_ = lean_uint64_xor(v_fold_321_, v___x_323_);
v___x_325_ = lean_uint64_to_usize(v___x_324_);
v___x_326_ = lean_usize_of_nat(v___x_317_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_sub(v___x_326_, v___x_327_);
v___x_329_ = lean_usize_land(v___x_325_, v___x_328_);
v_bkt_330_ = lean_array_uget_borrowed(v_buckets_316_, v___x_329_);
v___x_331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_313_, v_bkt_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_352_; 
lean_inc_ref(v_buckets_316_);
lean_inc(v_size_315_);
v_isSharedCheck_352_ = !lean_is_exclusive(v_m_312_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_353_ = lean_ctor_get(v_m_312_, 1);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_m_312_, 0);
lean_dec(v_unused_354_);
v___x_333_ = v_m_312_;
v_isShared_334_ = v_isSharedCheck_352_;
goto v_resetjp_332_;
}
else
{
lean_dec(v_m_312_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_352_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_size_x27_336_; lean_object* v___x_337_; lean_object* v_buckets_x27_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v_size_x27_336_ = lean_nat_add(v_size_315_, v___x_335_);
lean_dec(v_size_315_);
lean_inc(v_bkt_330_);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v_a_313_);
lean_ctor_set(v___x_337_, 1, v_b_314_);
lean_ctor_set(v___x_337_, 2, v_bkt_330_);
v_buckets_x27_338_ = lean_array_uset(v_buckets_316_, v___x_329_, v___x_337_);
v___x_339_ = lean_unsigned_to_nat(4u);
v___x_340_ = lean_nat_mul(v_size_x27_336_, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(3u);
v___x_342_ = lean_nat_div(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_array_get_size(v_buckets_x27_338_);
v___x_344_ = lean_nat_dec_le(v___x_342_, v___x_343_);
lean_dec(v___x_342_);
if (v___x_344_ == 0)
{
lean_object* v_val_345_; lean_object* v___x_347_; 
v_val_345_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_buckets_x27_338_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_val_345_);
lean_ctor_set(v___x_333_, 0, v_size_x27_336_);
v___x_347_ = v___x_333_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_size_x27_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_val_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v___x_350_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_buckets_x27_338_);
lean_ctor_set(v___x_333_, 0, v_size_x27_336_);
v___x_350_ = v___x_333_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_size_x27_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_buckets_x27_338_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_dec(v_b_314_);
lean_dec_ref(v_a_313_);
return v_m_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(lean_object* v_mvarId_359_, lean_object* v_e_360_, lean_object* v_a_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_d_372_; lean_object* v_b_373_; lean_object* v___y_374_; uint8_t v___x_380_; 
v___x_380_ = l_Lean_Expr_hasExprMVar(v_e_360_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec_ref(v_e_360_);
v___x_381_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_361_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_a_361_, v_e_360_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_box(0);
lean_inc_ref(v_e_360_);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_a_361_, v_e_360_, v___x_385_);
switch(lean_obj_tag(v_e_360_))
{
case 11:
{
lean_object* v_struct_387_; 
v_struct_387_ = lean_ctor_get(v_e_360_, 2);
lean_inc_ref(v_struct_387_);
lean_dec_ref_known(v_e_360_, 3);
v_e_360_ = v_struct_387_;
v_a_361_ = v___x_386_;
goto _start;
}
case 7:
{
lean_object* v_binderType_389_; lean_object* v_body_390_; 
v_binderType_389_ = lean_ctor_get(v_e_360_, 1);
lean_inc_ref(v_binderType_389_);
v_body_390_ = lean_ctor_get(v_e_360_, 2);
lean_inc_ref(v_body_390_);
lean_dec_ref_known(v_e_360_, 3);
v_d_372_ = v_binderType_389_;
v_b_373_ = v_body_390_;
v___y_374_ = v___x_386_;
goto v___jp_371_;
}
case 6:
{
lean_object* v_binderType_391_; lean_object* v_body_392_; 
v_binderType_391_ = lean_ctor_get(v_e_360_, 1);
lean_inc_ref(v_binderType_391_);
v_body_392_ = lean_ctor_get(v_e_360_, 2);
lean_inc_ref(v_body_392_);
lean_dec_ref_known(v_e_360_, 3);
v_d_372_ = v_binderType_391_;
v_b_373_ = v_body_392_;
v___y_374_ = v___x_386_;
goto v___jp_371_;
}
case 8:
{
lean_object* v_type_393_; lean_object* v_value_394_; lean_object* v_body_395_; lean_object* v___x_396_; 
v_type_393_ = lean_ctor_get(v_e_360_, 1);
lean_inc_ref(v_type_393_);
v_value_394_ = lean_ctor_get(v_e_360_, 2);
lean_inc_ref(v_value_394_);
v_body_395_ = lean_ctor_get(v_e_360_, 3);
lean_inc_ref(v_body_395_);
lean_dec_ref_known(v_e_360_, 4);
v___x_396_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_359_, v_type_393_, v___x_386_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
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
v___x_400_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_359_, v_value_394_, v_snd_399_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
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
v_e_360_ = v_body_395_;
v_a_361_ = v_snd_403_;
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
v_expr_405_ = lean_ctor_get(v_e_360_, 1);
lean_inc_ref(v_expr_405_);
lean_dec_ref_known(v_e_360_, 2);
v_e_360_ = v_expr_405_;
v_a_361_ = v___x_386_;
goto _start;
}
case 5:
{
lean_object* v_fn_407_; lean_object* v_arg_408_; lean_object* v___x_409_; 
v_fn_407_ = lean_ctor_get(v_e_360_, 0);
lean_inc_ref(v_fn_407_);
v_arg_408_ = lean_ctor_get(v_e_360_, 1);
lean_inc_ref(v_arg_408_);
lean_dec_ref_known(v_e_360_, 2);
v___x_409_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_359_, v_fn_407_, v___x_386_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
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
v_e_360_ = v_arg_408_;
v_a_361_ = v_snd_412_;
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
v_mvarId_414_ = lean_ctor_get(v_e_360_, 0);
lean_inc(v_mvarId_414_);
lean_dec_ref_known(v_e_360_, 1);
v___x_415_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_359_, v_mvarId_414_, v___x_386_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
return v___x_415_;
}
default: 
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_e_360_);
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
lean_dec_ref(v_e_360_);
v___x_419_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_a_361_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
v___jp_371_:
{
lean_object* v___x_375_; 
v___x_375_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_359_, v_d_372_, v___y_374_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v_fst_377_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
v_fst_377_ = lean_ctor_get(v_a_376_, 0);
if (lean_obj_tag(v_fst_377_) == 0)
{
lean_dec(v_a_376_);
lean_dec_ref(v_b_373_);
return v___x_375_;
}
else
{
lean_object* v_snd_378_; 
lean_dec_ref_known(v___x_375_, 1);
v_snd_378_ = lean_ctor_get(v_a_376_, 1);
lean_inc(v_snd_378_);
lean_dec(v_a_376_);
v_e_360_ = v_b_373_;
v_a_361_ = v_snd_378_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_373_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(lean_object* v_mvarId_422_, lean_object* v_mvarId_x27_423_, lean_object* v_a_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_instBEqMVarId_beq(v_mvarId_422_, v_mvarId_x27_423_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_x27_423_, v_a_424_, v___y_430_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_519_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_519_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_519_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_519_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_fst_440_; 
v_fst_440_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_fst_440_);
if (lean_obj_tag(v_fst_440_) == 0)
{
lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_mvarId_x27_423_);
v_snd_441_ = lean_ctor_get(v_a_436_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_a_436_, 0);
lean_dec(v_unused_460_);
v___x_443_ = v_a_436_;
v_isShared_444_ = v_isSharedCheck_459_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_dec(v_a_436_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_459_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_458_; 
v_a_445_ = lean_ctor_get(v_fst_440_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_fst_440_);
if (v_isSharedCheck_458_ == 0)
{
v___x_447_ = v_fst_440_;
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v_fst_440_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_457_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_450_);
v___x_452_ = v___x_443_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_snd_441_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_452_);
v___x_454_ = v___x_438_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
else
{
lean_object* v_a_461_; 
lean_del_object(v___x_438_);
v_a_461_ = lean_ctor_get(v_fst_440_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v_fst_440_, 1);
if (lean_obj_tag(v_a_461_) == 0)
{
lean_object* v_snd_462_; lean_object* v___x_463_; 
v_snd_462_ = lean_ctor_get(v_a_436_, 1);
lean_inc(v_snd_462_);
lean_dec(v_a_436_);
v___x_463_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_x27_423_, v_snd_462_, v___y_430_);
lean_dec(v_mvarId_x27_423_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_507_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_507_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_507_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_507_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_fst_468_; 
v_fst_468_ = lean_ctor_get(v_a_464_, 0);
lean_inc(v_fst_468_);
if (lean_obj_tag(v_fst_468_) == 0)
{
lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_487_; 
v_snd_469_ = lean_ctor_get(v_a_464_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_464_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_a_464_, 0);
lean_dec(v_unused_488_);
v___x_471_ = v_a_464_;
v_isShared_472_ = v_isSharedCheck_487_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_dec(v_a_464_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_487_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_486_; 
v_a_473_ = lean_ctor_get(v_fst_468_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_fst_468_);
if (v_isSharedCheck_486_ == 0)
{
v___x_475_ = v_fst_468_;
v_isShared_476_ = v_isSharedCheck_486_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v_fst_468_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_486_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_485_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_478_);
v___x_480_ = v___x_471_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_snd_469_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_480_);
v___x_482_ = v___x_466_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
else
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v_fst_468_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v_fst_468_, 1);
if (lean_obj_tag(v_a_489_) == 0)
{
lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_501_; 
v_snd_490_ = lean_ctor_get(v_a_464_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_a_464_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_a_464_, 0);
lean_dec(v_unused_502_);
v___x_492_ = v_a_464_;
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_dec(v_a_464_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0));
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_snd_490_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_496_);
v___x_498_ = v___x_466_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_val_503_; lean_object* v_snd_504_; lean_object* v_mvarIdPending_505_; 
lean_del_object(v___x_466_);
v_val_503_ = lean_ctor_get(v_a_489_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_489_, 1);
v_snd_504_ = lean_ctor_get(v_a_464_, 1);
lean_inc(v_snd_504_);
lean_dec(v_a_464_);
v_mvarIdPending_505_ = lean_ctor_get(v_val_503_, 1);
lean_inc(v_mvarIdPending_505_);
lean_dec(v_val_503_);
v_mvarId_x27_423_ = v_mvarIdPending_505_;
v_a_424_ = v_snd_504_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_463_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_463_);
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
lean_object* v_snd_516_; lean_object* v_val_517_; lean_object* v___x_518_; 
lean_dec(v_mvarId_x27_423_);
v_snd_516_ = lean_ctor_get(v_a_436_, 1);
lean_inc(v_snd_516_);
lean_dec(v_a_436_);
v_val_517_ = lean_ctor_get(v_a_461_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_a_461_, 1);
v___x_518_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_422_, v_val_517_, v_snd_516_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_518_;
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_mvarId_x27_423_);
v_a_520_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_435_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_435_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_mvarId_x27_423_);
v___x_528_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1));
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_a_424_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___boxed(lean_object* v_mvarId_531_, lean_object* v_mvarId_x27_532_, lean_object* v_a_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_531_, v_mvarId_x27_532_, v_a_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v_mvarId_531_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2___boxed(lean_object* v_mvarId_544_, lean_object* v_e_545_, lean_object* v_a_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_544_, v_e_545_, v_a_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v_mvarId_544_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_unsigned_to_nat(16u);
v___x_559_ = lean_mk_array(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(lean_object* v_mvarId_563_, lean_object* v_e_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = l_Lean_Expr_hasExprMVar(v_e_564_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_e_564_);
v___x_575_ = 1;
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1);
v___x_579_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_563_, v_e_564_, v___x_578_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_594_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_594_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_fst_584_; 
v_fst_584_ = lean_ctor_get(v_a_580_, 0);
lean_inc(v_fst_584_);
lean_dec(v_a_580_);
if (lean_obj_tag(v_fst_584_) == 0)
{
uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec_ref_known(v_fst_584_, 1);
v___x_585_ = 0;
v___x_586_ = lean_box(v___x_585_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_586_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec_ref_known(v_fst_584_, 1);
v___x_590_ = lean_box(v___x_574_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_590_);
v___x_592_ = v___x_582_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_579_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_579_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(lean_object* v_mvarId_603_, lean_object* v_e_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_603_, v_e_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_mvarId_603_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(lean_object* v___x_615_, lean_object* v___x_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
if (lean_obj_tag(v_a_617_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = l_List_reverse___redArg(v_a_618_);
return v___x_619_;
}
else
{
lean_object* v_head_620_; lean_object* v_tail_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
v_head_620_ = lean_ctor_get(v_a_617_, 0);
v_tail_621_ = lean_ctor_get(v_a_617_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_623_ = v_a_617_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tail_621_);
lean_inc(v_head_620_);
lean_dec(v_a_617_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v_index_626_; uint8_t v___x_627_; 
lean_inc(v_head_620_);
v___x_625_ = l_Lean_MetavarContext_getDecl(v___x_615_, v_head_620_);
v_index_626_ = lean_ctor_get(v___x_625_, 6);
lean_inc(v_index_626_);
lean_dec_ref(v___x_625_);
v___x_627_ = lean_nat_dec_le(v___x_616_, v_index_626_);
lean_dec(v_index_626_);
if (v___x_627_ == 0)
{
lean_del_object(v___x_623_);
lean_dec(v_head_620_);
v_a_617_ = v_tail_621_;
goto _start;
}
else
{
lean_object* v___x_630_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_a_618_);
v___x_630_ = v___x_623_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_head_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_a_618_);
v___x_630_ = v_reuseFailAlloc_632_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
v_a_617_ = v_tail_621_;
v_a_618_ = v___x_630_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v___x_634_, v___x_635_, v_a_636_, v_a_637_);
lean_dec(v___x_635_);
lean_dec_ref(v___x_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(lean_object* v_msgData_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; lean_object* v___x_647_; lean_object* v_mctx_648_; lean_object* v_lctx_649_; lean_object* v_options_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_645_ = lean_st_ref_get(v___y_643_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
v___x_647_ = lean_st_ref_get(v___y_641_);
v_mctx_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_mctx_648_);
lean_dec(v___x_647_);
v_lctx_649_ = lean_ctor_get(v___y_640_, 2);
v_options_650_ = lean_ctor_get(v___y_642_, 2);
lean_inc_ref(v_options_650_);
lean_inc_ref(v_lctx_649_);
v___x_651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_651_, 0, v_env_646_);
lean_ctor_set(v___x_651_, 1, v_mctx_648_);
lean_ctor_set(v___x_651_, 2, v_lctx_649_);
lean_ctor_set(v___x_651_, 3, v_options_650_);
v___x_652_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_msgData_639_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(lean_object* v_msgData_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_ref_667_; lean_object* v___x_668_; lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_ref_667_ = lean_ctor_get(v___y_664_, 5);
v___x_668_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc(v_ref_667_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_ref_667_);
lean_ctor_set(v___x_673_, 1, v_a_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 1);
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(lean_object* v_msg_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(lean_object* v_ref_685_, lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_fileName_696_; lean_object* v_fileMap_697_; lean_object* v_options_698_; lean_object* v_currRecDepth_699_; lean_object* v_maxRecDepth_700_; lean_object* v_ref_701_; lean_object* v_currNamespace_702_; lean_object* v_openDecls_703_; lean_object* v_initHeartbeats_704_; lean_object* v_maxHeartbeats_705_; lean_object* v_quotContext_706_; lean_object* v_currMacroScope_707_; uint8_t v_diag_708_; lean_object* v_cancelTk_x3f_709_; uint8_t v_suppressElabErrors_710_; lean_object* v_inheritedTraceOptions_711_; lean_object* v_ref_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_fileName_696_ = lean_ctor_get(v___y_693_, 0);
v_fileMap_697_ = lean_ctor_get(v___y_693_, 1);
v_options_698_ = lean_ctor_get(v___y_693_, 2);
v_currRecDepth_699_ = lean_ctor_get(v___y_693_, 3);
v_maxRecDepth_700_ = lean_ctor_get(v___y_693_, 4);
v_ref_701_ = lean_ctor_get(v___y_693_, 5);
v_currNamespace_702_ = lean_ctor_get(v___y_693_, 6);
v_openDecls_703_ = lean_ctor_get(v___y_693_, 7);
v_initHeartbeats_704_ = lean_ctor_get(v___y_693_, 8);
v_maxHeartbeats_705_ = lean_ctor_get(v___y_693_, 9);
v_quotContext_706_ = lean_ctor_get(v___y_693_, 10);
v_currMacroScope_707_ = lean_ctor_get(v___y_693_, 11);
v_diag_708_ = lean_ctor_get_uint8(v___y_693_, sizeof(void*)*14);
v_cancelTk_x3f_709_ = lean_ctor_get(v___y_693_, 12);
v_suppressElabErrors_710_ = lean_ctor_get_uint8(v___y_693_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_711_ = lean_ctor_get(v___y_693_, 13);
v_ref_712_ = l_Lean_replaceRef(v_ref_685_, v_ref_701_);
lean_inc_ref(v_inheritedTraceOptions_711_);
lean_inc(v_cancelTk_x3f_709_);
lean_inc(v_currMacroScope_707_);
lean_inc(v_quotContext_706_);
lean_inc(v_maxHeartbeats_705_);
lean_inc(v_initHeartbeats_704_);
lean_inc(v_openDecls_703_);
lean_inc(v_currNamespace_702_);
lean_inc(v_maxRecDepth_700_);
lean_inc(v_currRecDepth_699_);
lean_inc_ref(v_options_698_);
lean_inc_ref(v_fileMap_697_);
lean_inc_ref(v_fileName_696_);
v___x_713_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_713_, 0, v_fileName_696_);
lean_ctor_set(v___x_713_, 1, v_fileMap_697_);
lean_ctor_set(v___x_713_, 2, v_options_698_);
lean_ctor_set(v___x_713_, 3, v_currRecDepth_699_);
lean_ctor_set(v___x_713_, 4, v_maxRecDepth_700_);
lean_ctor_set(v___x_713_, 5, v_ref_712_);
lean_ctor_set(v___x_713_, 6, v_currNamespace_702_);
lean_ctor_set(v___x_713_, 7, v_openDecls_703_);
lean_ctor_set(v___x_713_, 8, v_initHeartbeats_704_);
lean_ctor_set(v___x_713_, 9, v_maxHeartbeats_705_);
lean_ctor_set(v___x_713_, 10, v_quotContext_706_);
lean_ctor_set(v___x_713_, 11, v_currMacroScope_707_);
lean_ctor_set(v___x_713_, 12, v_cancelTk_x3f_709_);
lean_ctor_set(v___x_713_, 13, v_inheritedTraceOptions_711_);
lean_ctor_set_uint8(v___x_713_, sizeof(void*)*14, v_diag_708_);
lean_ctor_set_uint8(v___x_713_, sizeof(void*)*14 + 1, v_suppressElabErrors_710_);
v___x_714_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_686_, v___y_691_, v___y_692_, v___x_713_, v___y_694_);
lean_dec_ref_known(v___x_713_, 14);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(lean_object* v_ref_715_, lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_715_, v_msg_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v_ref_715_);
return v_res_726_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__1(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__0));
v___x_729_ = l_Lean_stringToMessageData(v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewrite___closed__3(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewrite___closed__2));
v___x_732_ = l_Lean_stringToMessageData(v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite(lean_object* v_mvarId_733_, lean_object* v_e_734_, lean_object* v_stx_735_, uint8_t v_symm_736_, lean_object* v_config_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; 
v___x_747_ = lean_st_ref_get(v_a_743_);
v___x_748_ = lean_box(0);
v___x_749_ = 1;
lean_inc(v_stx_735_);
v___x_750_ = l_Lean_Elab_Tactic_elabTerm(v_stx_735_, v___x_748_, v___x_749_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_mctx_751_; lean_object* v_a_752_; lean_object* v_mvarCounter_753_; lean_object* v___x_754_; lean_object* v___f_755_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___x_825_; 
v_mctx_751_ = lean_ctor_get(v___x_747_, 0);
lean_inc_ref(v_mctx_751_);
lean_dec(v___x_747_);
v_a_752_ = lean_ctor_get(v___x_750_, 0);
lean_inc_n(v_a_752_, 2);
lean_dec_ref_known(v___x_750_, 1);
v_mvarCounter_753_ = lean_ctor_get(v_mctx_751_, 3);
lean_inc(v_mvarCounter_753_);
lean_dec_ref(v_mctx_751_);
v___x_754_ = lean_box(v_symm_736_);
lean_inc_ref(v_e_734_);
lean_inc(v_mvarId_733_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed), 14, 5);
lean_closure_set(v___f_755_, 0, v_mvarId_733_);
lean_closure_set(v___f_755_, 1, v_e_734_);
lean_closure_set(v___f_755_, 2, v_a_752_);
lean_closure_set(v___f_755_, 3, v___x_754_);
lean_closure_set(v___f_755_, 4, v_config_737_);
v___x_825_ = l_Lean_Expr_hasSyntheticSorry(v_a_752_);
if (v___x_825_ == 0)
{
v___y_789_ = v_a_738_;
v___y_790_ = v_a_739_;
v___y_791_ = v_a_740_;
v___y_792_ = v_a_741_;
v___y_793_ = v_a_742_;
v___y_794_ = v_a_743_;
v___y_795_ = v_a_744_;
v___y_796_ = v_a_745_;
goto v___jp_788_;
}
else
{
lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v___f_755_);
lean_dec(v_mvarCounter_753_);
lean_dec(v_a_752_);
lean_dec(v_stx_735_);
lean_dec_ref(v_e_734_);
lean_dec(v_mvarId_733_);
v___x_826_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
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
v___jp_756_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_734_, v___f_755_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_787_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_787_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_787_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_787_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v_mctx_771_; lean_object* v_eNew_772_; lean_object* v_eqProof_773_; lean_object* v_mvarIds_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
v___x_770_ = lean_st_ref_get(v___y_762_);
v_mctx_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_ref(v_mctx_771_);
lean_dec(v___x_770_);
v_eNew_772_ = lean_ctor_get(v_a_766_, 0);
v_eqProof_773_ = lean_ctor_get(v_a_766_, 1);
v_mvarIds_774_ = lean_ctor_get(v_a_766_, 2);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_766_);
if (v_isSharedCheck_786_ == 0)
{
v___x_776_ = v_a_766_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_mvarIds_774_);
lean_inc(v_eqProof_773_);
lean_inc(v_eNew_772_);
lean_dec(v_a_766_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = lean_box(0);
v___x_779_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(v_mctx_771_, v_mvarCounter_753_, v_mvarIds_774_, v___x_778_);
lean_dec(v_mvarCounter_753_);
lean_dec_ref(v_mctx_771_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_eNew_772_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_eqProof_773_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v___x_779_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_781_);
v___x_783_ = v___x_768_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_dec(v_mvarCounter_753_);
return v___x_765_;
}
}
v___jp_788_:
{
lean_object* v___x_797_; 
lean_inc(v_a_752_);
v___x_797_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(v_mvarId_733_, v_a_752_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; uint8_t v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = lean_unbox(v_a_798_);
lean_dec(v_a_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v___f_755_);
lean_dec(v_mvarCounter_753_);
lean_dec_ref(v_e_734_);
v___x_800_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__1, &l_Lean_Elab_Tactic_elabRewrite___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__1);
v___x_801_ = l_Lean_indentExpr(v_a_752_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewrite___closed__3, &l_Lean_Elab_Tactic_elabRewrite___closed__3_once, _init_l_Lean_Elab_Tactic_elabRewrite___closed__3);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_Expr_mvar___override(v_mvarId_733_);
v___x_806_ = l_Lean_MessageData_ofExpr(v___x_805_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_735_, v___x_807_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v_stx_735_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
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
else
{
lean_dec(v_a_752_);
lean_dec(v_stx_735_);
lean_dec(v_mvarId_733_);
v___y_757_ = v___y_789_;
v___y_758_ = v___y_790_;
v___y_759_ = v___y_791_;
v___y_760_ = v___y_792_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
v___y_763_ = v___y_795_;
v___y_764_ = v___y_796_;
goto v___jp_756_;
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v___f_755_);
lean_dec(v_mvarCounter_753_);
lean_dec(v_a_752_);
lean_dec(v_stx_735_);
lean_dec_ref(v_e_734_);
lean_dec(v_mvarId_733_);
v_a_817_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_797_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_797_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v___x_747_);
lean_dec_ref(v_config_737_);
lean_dec(v_stx_735_);
lean_dec_ref(v_e_734_);
lean_dec(v_mvarId_733_);
v_a_835_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_750_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_750_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewrite___boxed(lean_object* v_mvarId_843_, lean_object* v_e_844_, lean_object* v_stx_845_, lean_object* v_symm_846_, lean_object* v_config_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
uint8_t v_symm_boxed_857_; lean_object* v_res_858_; 
v_symm_boxed_857_ = lean_unbox(v_symm_846_);
v_res_858_ = l_Lean_Elab_Tactic_elabRewrite(v_mvarId_843_, v_e_844_, v_stx_845_, v_symm_boxed_857_, v_config_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(lean_object* v_00_u03b1_859_, lean_object* v_ref_860_, lean_object* v_msg_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_ref_860_, v_msg_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(lean_object* v_00_u03b1_872_, lean_object* v_ref_873_, lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(v_00_u03b1_872_, v_ref_873_, v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v_ref_873_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(lean_object* v_00_u03b1_885_, lean_object* v_msg_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_886_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(lean_object* v_00_u03b1_897_, lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_897_, v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_908_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_910_, v_a_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_913_, lean_object* v_m_914_, lean_object* v_a_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_913_, v_m_914_, v_a_915_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v_m_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_a_920_, lean_object* v_b_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_919_, v_a_920_, v_b_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(lean_object* v_mvarId_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_923_, v___y_924_, v___y_930_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(lean_object* v_mvarId_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v_mvarId_935_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(lean_object* v_mvarId_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_947_, v___y_948_, v___y_954_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(lean_object* v_mvarId_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v_mvarId_959_);
return v_res_970_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_971_, lean_object* v_a_972_, lean_object* v_x_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_975_, lean_object* v_a_976_, lean_object* v_x_977_){
_start:
{
uint8_t v_res_978_; lean_object* v_r_979_; 
v_res_978_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_975_, v_a_976_, v_x_977_);
lean_dec(v_x_977_);
lean_dec_ref(v_a_976_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_980_, lean_object* v_data_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_983_, lean_object* v_i_984_, lean_object* v_source_985_, lean_object* v_target_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_984_, v_source_985_, v_target_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(lean_object* v_mvarId_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_992_, v_x_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
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
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(lean_object* v_mvarId_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1016_, v_x_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(lean_object* v_00_u03b1_1024_, lean_object* v_mvarId_1025_, lean_object* v_x_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_mvarId_1025_, v_x_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_mvarId_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(v_00_u03b1_1033_, v_mvarId_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1041_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_array_get_size(v_keys_1042_);
v___x_1046_ = lean_nat_dec_lt(v_i_1043_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec(v_i_1043_);
return v___x_1046_;
}
else
{
lean_object* v_k_x27_1047_; uint8_t v___x_1048_; 
v_k_x27_1047_ = lean_array_fget_borrowed(v_keys_1042_, v_i_1043_);
v___x_1048_ = l_Lean_instBEqMVarId_beq(v_k_1044_, v_k_x27_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_add(v_i_1043_, v___x_1049_);
lean_dec(v_i_1043_);
v_i_1043_ = v___x_1050_;
goto _start;
}
else
{
lean_dec(v_i_1043_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1052_, lean_object* v_i_1053_, lean_object* v_k_1054_){
_start:
{
uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_res_1055_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1052_, v_i_1053_, v_k_1054_);
lean_dec(v_k_1054_);
lean_dec_ref(v_keys_1052_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; 
v___x_1057_ = ((size_t)5ULL);
v___x_1058_ = ((size_t)1ULL);
v___x_1059_ = lean_usize_shift_left(v___x_1058_, v___x_1057_);
return v___x_1059_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; 
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1062_ = lean_usize_sub(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1063_, size_t v_x_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v_es_1066_; lean_object* v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; lean_object* v_j_1071_; lean_object* v___x_1072_; 
v_es_1066_ = lean_ctor_get(v_x_1063_, 0);
v___x_1067_ = lean_box(2);
v___x_1068_ = ((size_t)5ULL);
v___x_1069_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1070_ = lean_usize_land(v_x_1064_, v___x_1069_);
v_j_1071_ = lean_usize_to_nat(v___x_1070_);
v___x_1072_ = lean_array_get_borrowed(v___x_1067_, v_es_1066_, v_j_1071_);
lean_dec(v_j_1071_);
switch(lean_obj_tag(v___x_1072_))
{
case 0:
{
lean_object* v_key_1073_; uint8_t v___x_1074_; 
v_key_1073_ = lean_ctor_get(v___x_1072_, 0);
v___x_1074_ = l_Lean_instBEqMVarId_beq(v_x_1065_, v_key_1073_);
return v___x_1074_;
}
case 1:
{
lean_object* v_node_1075_; size_t v___x_1076_; 
v_node_1075_ = lean_ctor_get(v___x_1072_, 0);
v___x_1076_ = lean_usize_shift_right(v_x_1064_, v___x_1068_);
v_x_1063_ = v_node_1075_;
v_x_1064_ = v___x_1076_;
goto _start;
}
default: 
{
uint8_t v___x_1078_; 
v___x_1078_ = 0;
return v___x_1078_;
}
}
}
else
{
lean_object* v_ks_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_ks_1079_ = lean_ctor_get(v_x_1063_, 0);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_1079_, v___x_1080_, v_x_1065_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
size_t v_x_1972__boxed_1085_; uint8_t v_res_1086_; lean_object* v_r_1087_; 
v_x_1972__boxed_1085_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_res_1086_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1082_, v_x_1972__boxed_1085_, v_x_1084_);
lean_dec(v_x_1084_);
lean_dec_ref(v_x_1082_);
v_r_1087_ = lean_box(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
uint64_t v___x_1090_; size_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = l_Lean_instHashableMVarId_hash(v_x_1089_);
v___x_1091_ = lean_uint64_to_usize(v___x_1090_);
v___x_1092_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1088_, v___x_1091_, v_x_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1093_, v_x_1094_);
lean_dec(v_x_1094_);
lean_dec_ref(v_x_1093_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(lean_object* v_mvarId_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v_mctx_1101_; lean_object* v_eAssignment_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1100_ = lean_st_ref_get(v___y_1098_);
v_mctx_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_mctx_1101_);
lean_dec(v___x_1100_);
v_eAssignment_1102_ = lean_ctor_get(v_mctx_1101_, 8);
lean_inc_ref(v_eAssignment_1102_);
lean_dec_ref(v_mctx_1101_);
v___x_1103_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_1102_, v_mvarId_1097_);
lean_dec_ref(v_eAssignment_1102_);
v___x_1104_ = lean_box(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(lean_object* v_mvarId_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec(v_mvarId_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_x_1111_);
return v___x_1117_;
}
else
{
lean_object* v_head_1118_; lean_object* v_tail_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1132_; 
v_head_1118_ = lean_ctor_get(v_x_1110_, 0);
v_tail_1119_ = lean_ctor_get(v_x_1110_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1121_ = v_x_1110_;
v_isShared_1122_ = v_isSharedCheck_1132_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_tail_1119_);
lean_inc(v_head_1118_);
lean_dec(v_x_1110_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1132_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1128_; lean_object* v_a_1129_; uint8_t v___x_1130_; 
v___x_1128_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_1118_, v___y_1113_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = lean_unbox(v_a_1129_);
lean_dec(v_a_1129_);
if (v___x_1130_ == 0)
{
goto v___jp_1123_;
}
else
{
lean_del_object(v___x_1121_);
lean_dec(v_head_1118_);
v_x_1110_ = v_tail_1119_;
goto _start;
}
v___jp_1123_:
{
lean_object* v___x_1125_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_x_1111_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_head_1118_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_x_1111_);
v___x_1125_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v_x_1110_ = v_tail_1119_;
v_x_1111_ = v___x_1125_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_x_1133_, v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(lean_object* v_head_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
lean_inc(v_head_1141_);
v___x_1147_ = l_Lean_MVarId_getType(v_head_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = l_Lean_Meta_isProp(v_a_1148_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1161_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___x_1154_; 
v___x_1154_ = lean_unbox(v_a_1150_);
lean_dec(v_a_1150_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec(v_head_1141_);
v___x_1155_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
uint8_t v___x_1159_; lean_object* v___x_1160_; 
lean_del_object(v___x_1152_);
v___x_1159_ = 2;
v___x_1160_ = l_Lean_MVarId_setKind___redArg(v_head_1141_, v___x_1159_, v___y_1143_);
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_head_1141_);
v_a_1162_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1149_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1149_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_head_1141_);
v_a_1170_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1147_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1147_);
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(lean_object* v_head_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(v_head_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(lean_object* v_as_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
if (lean_obj_tag(v_as_1185_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
else
{
lean_object* v_head_1193_; lean_object* v_tail_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; 
v_head_1193_ = lean_ctor_get(v_as_1185_, 0);
lean_inc_n(v_head_1193_, 2);
v_tail_1194_ = lean_ctor_get(v_as_1185_, 1);
lean_inc(v_tail_1194_);
lean_dec_ref_known(v_as_1185_, 2);
v___f_1195_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1195_, 0, v_head_1193_);
v___x_1196_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_1193_, v___f_1195_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_dec_ref_known(v___x_1196_, 1);
v_as_1185_ = v_tail_1194_;
goto _start;
}
else
{
lean_dec(v_tail_1194_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(lean_object* v_as_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_as_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite(lean_object* v_r_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_eNew_1211_; lean_object* v_eqProof_1212_; lean_object* v_mvarIds_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1252_; 
v_eNew_1211_ = lean_ctor_get(v_r_1205_, 0);
v_eqProof_1212_ = lean_ctor_get(v_r_1205_, 1);
v_mvarIds_1213_ = lean_ctor_get(v_r_1205_, 2);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_r_1205_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1215_ = v_r_1205_;
v_isShared_1216_ = v_isSharedCheck_1252_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_mvarIds_1213_);
lean_inc(v_eqProof_1212_);
lean_inc(v_eNew_1211_);
lean_dec(v_r_1205_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1252_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_a_1218_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(v_mvarIds_1213_, v___x_1239_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1242_ = l_List_reverse___redArg(v_a_1241_);
v_a_1218_ = v___x_1242_;
goto v___jp_1217_;
}
else
{
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1243_; 
v_a_1243_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1240_, 1);
v_a_1218_ = v_a_1243_;
goto v___jp_1217_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_del_object(v___x_1215_);
lean_dec_ref(v_eqProof_1212_);
lean_dec_ref(v_eNew_1211_);
v_a_1244_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1240_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1240_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
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
v___jp_1217_:
{
lean_object* v___x_1219_; 
lean_inc(v_a_1218_);
v___x_1219_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(v_a_1218_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1229_; 
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1219_, 0);
lean_dec(v_unused_1230_);
v___x_1221_ = v___x_1219_;
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
else
{
lean_dec(v___x_1219_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 2, v_a_1218_);
v___x_1224_ = v___x_1215_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_eNew_1211_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_eqProof_1212_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_a_1218_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1218_);
lean_del_object(v___x_1215_);
lean_dec_ref(v_eqProof_1212_);
lean_dec_ref(v_eNew_1211_);
v_a_1231_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1219_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1219_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_finishElabRewrite___boxed(lean_object* v_r_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Elab_Tactic_finishElabRewrite(v_r_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(lean_object* v_mvarId_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_mvarId_1260_, v___y_1262_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(lean_object* v_mvarId_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(v_mvarId_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v_mvarId_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(lean_object* v_00_u03b2_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_1275_, v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_1278_, v_x_1279_, v_x_1280_);
lean_dec(v_x_1280_);
lean_dec_ref(v_x_1279_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1283_, lean_object* v_x_1284_, size_t v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_1284_, v_x_1285_, v_x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
size_t v_x_2317__boxed_1292_; uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_x_2317__boxed_1292_ = lean_unbox_usize(v_x_1290_);
lean_dec(v_x_1290_);
v_res_1293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_1288_, v_x_1289_, v_x_2317__boxed_1292_, v_x_1291_);
lean_dec(v_x_1291_);
lean_dec_ref(v_x_1289_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1295_, lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_heq_1298_, lean_object* v_i_1299_, lean_object* v_k_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1296_, v_i_1299_, v_k_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_keys_1303_, lean_object* v_vals_1304_, lean_object* v_heq_1305_, lean_object* v_i_1306_, lean_object* v_k_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1302_, v_keys_1303_, v_vals_1304_, v_heq_1305_, v_i_1306_, v_k_1307_);
lean_dec(v_k_1307_);
lean_dec_ref(v_vals_1304_);
lean_dec_ref(v_keys_1303_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* v_stx_1310_, uint8_t v_symm_1311_, lean_object* v_config_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1314_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1323_, v_a_1325_, v_stx_1310_, v_symm_1311_, v_config_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_a_1323_);
lean_dec_ref(v_config_1312_);
lean_dec(v_stx_1310_);
v_a_1327_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1324_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1324_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
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
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_config_1312_);
lean_dec(v_stx_1310_);
v_a_1335_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1322_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1322_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* v_stx_1343_, lean_object* v_symm_1344_, lean_object* v_config_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_symm_boxed_1355_; lean_object* v_res_1356_; 
v_symm_boxed_1355_ = lean_unbox(v_symm_1344_);
v_res_1356_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(v_stx_1343_, v_symm_boxed_1355_, v_config_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* v_stx_1357_, uint8_t v_symm_1358_, lean_object* v_config_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1369_ = lean_box(v_symm_1358_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1370_, 0, v_stx_1357_);
lean_closure_set(v___f_1370_, 1, v___x_1369_);
lean_closure_set(v___f_1370_, 2, v_config_1359_);
v___x_1371_ = 1;
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
v___x_1372_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1372_, 0, lean_box(0));
lean_closure_set(v___x_1372_, 1, v___f_1370_);
lean_closure_set(v___x_1372_, 2, v_a_1360_);
lean_closure_set(v___x_1372_, 3, v_a_1361_);
v___x_1373_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1372_, v___x_1371_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1374_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1361_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_eNew_1379_; lean_object* v_eqProof_1380_; lean_object* v_mvarIds_1381_; lean_object* v___x_1382_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_eNew_1379_ = lean_ctor_get(v_a_1376_, 0);
lean_inc_ref(v_eNew_1379_);
v_eqProof_1380_ = lean_ctor_get(v_a_1376_, 1);
lean_inc_ref(v_eqProof_1380_);
v_mvarIds_1381_ = lean_ctor_get(v_a_1376_, 2);
lean_inc(v_mvarIds_1381_);
lean_dec(v_a_1376_);
v___x_1382_ = l_Lean_MVarId_replaceTargetEq(v_a_1378_, v_eNew_1379_, v_eqProof_1380_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_a_1383_);
lean_ctor_set(v___x_1384_, 1, v_mvarIds_1381_);
v___x_1385_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1384_, v_a_1361_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_mvarIds_1381_);
v_a_1386_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1382_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1382_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_a_1376_);
v_a_1394_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1377_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1377_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1375_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1375_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1373_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1373_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* v_stx_1418_, lean_object* v_symm_1419_, lean_object* v_config_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
uint8_t v_symm_boxed_1430_; lean_object* v_res_1431_; 
v_symm_boxed_1430_ = lean_unbox(v_symm_1419_);
v_res_1431_ = l_Lean_Elab_Tactic_rewriteTarget(v_stx_1418_, v_symm_boxed_1430_, v_config_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object* v_fvarId_1432_, lean_object* v_stx_1433_, uint8_t v_symm_1434_, lean_object* v_config_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1432_, v___y_1440_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1437_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = l_Lean_LocalDecl_type(v_a_1446_);
lean_dec(v_a_1446_);
v___x_1450_ = l_Lean_Elab_Tactic_elabRewrite(v_a_1448_, v___x_1449_, v_stx_1433_, v_symm_1434_, v_config_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1450_;
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_a_1446_);
lean_dec_ref(v_config_1435_);
lean_dec(v_stx_1433_);
v_a_1451_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1447_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1447_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v_config_1435_);
lean_dec(v_stx_1433_);
v_a_1459_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1445_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1445_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object* v_fvarId_1467_, lean_object* v_stx_1468_, lean_object* v_symm_1469_, lean_object* v_config_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v_symm_boxed_1480_; lean_object* v_res_1481_; 
v_symm_boxed_1480_ = lean_unbox(v_symm_1469_);
v_res_1481_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(v_fvarId_1467_, v_stx_1468_, v_symm_boxed_1480_, v_config_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object* v_eqProof_1482_, lean_object* v___x_1483_, lean_object* v_eNew_1484_, lean_object* v_a_1485_, lean_object* v_fvarId_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Meta_mkEqMP(v_eqProof_1482_, v___x_1483_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_eNew_1484_);
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Lean_MVarId_replace(v_a_1485_, v_fvarId_1486_, v_a_1493_, v___x_1494_, v___x_1495_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1496_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_fvarId_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_eNew_1484_);
v_a_1497_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1492_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1492_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object* v_eqProof_1505_, lean_object* v___x_1506_, lean_object* v_eNew_1507_, lean_object* v_a_1508_, lean_object* v_fvarId_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(v_eqProof_1505_, v___x_1506_, v_eNew_1507_, v_a_1508_, v_fvarId_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(lean_object* v___f_1516_, uint8_t v___x_1517_, lean_object* v_fvarId_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_inc(v___y_1520_);
v___x_1528_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(v___x_1528_, 0, lean_box(0));
lean_closure_set(v___x_1528_, 1, v___f_1516_);
lean_closure_set(v___x_1528_, 2, v___y_1519_);
lean_closure_set(v___x_1528_, 3, v___y_1520_);
v___x_1529_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1528_, v___x_1517_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Elab_Tactic_finishElabRewrite(v_a_1530_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1520_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v_eNew_1535_; lean_object* v_eqProof_1536_; lean_object* v_mvarIds_1537_; lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_n(v_a_1534_, 2);
lean_dec_ref_known(v___x_1533_, 1);
v_eNew_1535_ = lean_ctor_get(v_a_1532_, 0);
lean_inc_ref(v_eNew_1535_);
v_eqProof_1536_ = lean_ctor_get(v_a_1532_, 1);
lean_inc_ref(v_eqProof_1536_);
v_mvarIds_1537_ = lean_ctor_get(v_a_1532_, 2);
lean_inc(v_mvarIds_1537_);
lean_dec(v_a_1532_);
lean_inc(v_fvarId_1518_);
v___x_1538_ = l_Lean_mkFVar(v_fvarId_1518_);
v___f_1539_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed), 10, 5);
lean_closure_set(v___f_1539_, 0, v_eqProof_1536_);
lean_closure_set(v___f_1539_, 1, v___x_1538_);
lean_closure_set(v___f_1539_, 2, v_eNew_1535_);
lean_closure_set(v___f_1539_, 3, v_a_1534_);
lean_closure_set(v___f_1539_, 4, v_fvarId_1518_);
v___x_1540_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_1534_, v___f_1539_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v_mvarId_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v_mvarId_1542_ = lean_ctor_get(v_a_1541_, 1);
lean_inc(v_mvarId_1542_);
lean_dec(v_a_1541_);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_mvarId_1542_);
lean_ctor_set(v___x_1543_, 1, v_mvarIds_1537_);
v___x_1544_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1543_, v___y_1520_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1520_);
return v___x_1544_;
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_mvarIds_1537_);
lean_dec(v___y_1520_);
v_a_1545_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1540_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1540_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1532_);
lean_dec(v___y_1520_);
lean_dec(v_fvarId_1518_);
v_a_1553_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1533_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1533_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v___y_1520_);
lean_dec(v_fvarId_1518_);
v_a_1561_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1531_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1531_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v___y_1520_);
lean_dec(v_fvarId_1518_);
v_a_1569_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1529_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1529_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed(lean_object* v___f_1577_, lean_object* v___x_1578_, lean_object* v_fvarId_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v___x_1374__boxed_1589_; lean_object* v_res_1590_; 
v___x_1374__boxed_1589_ = lean_unbox(v___x_1578_);
v_res_1590_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(v___f_1577_, v___x_1374__boxed_1589_, v_fvarId_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* v_stx_1591_, uint8_t v_symm_1592_, lean_object* v_fvarId_1593_, lean_object* v_config_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1604_; lean_object* v___f_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; 
v___x_1604_ = lean_box(v_symm_1592_);
lean_inc(v_fvarId_1593_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1605_, 0, v_fvarId_1593_);
lean_closure_set(v___f_1605_, 1, v_stx_1591_);
lean_closure_set(v___f_1605_, 2, v___x_1604_);
lean_closure_set(v___f_1605_, 3, v_config_1594_);
v___x_1606_ = 1;
v___x_1607_ = lean_box(v___x_1606_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1608_, 0, v___f_1605_);
lean_closure_set(v___f_1608_, 1, v___x_1607_);
lean_closure_set(v___f_1608_, 2, v_fvarId_1593_);
v___x_1609_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1608_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* v_stx_1610_, lean_object* v_symm_1611_, lean_object* v_fvarId_1612_, lean_object* v_config_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_symm_boxed_1623_; lean_object* v_res_1624_; 
v_symm_boxed_1623_ = lean_unbox(v_symm_1611_);
v_res_1624_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_stx_1610_, v_symm_boxed_1623_, v_fvarId_1612_, v_config_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1624_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* v_x_1631_, uint8_t v_symm_1632_, lean_object* v_id_1633_, lean_object* v_declName_1634_, lean_object* v_hint_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
if (lean_obj_tag(v_a_1636_) == 0)
{
lean_object* v___x_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_x_1631_);
v___x_1646_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
v___x_1647_ = 0;
v___x_1648_ = l_Lean_MessageData_ofConstName(v_declName_1634_, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_hint_1635_);
v___x_1653_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_1652_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
return v___x_1653_;
}
else
{
lean_object* v_head_1654_; lean_object* v_tail_1655_; lean_object* v___x_1656_; 
v_head_1654_ = lean_ctor_get(v_a_1636_, 0);
lean_inc(v_head_1654_);
v_tail_1655_ = lean_ctor_get(v_a_1636_, 1);
lean_inc(v_tail_1655_);
lean_dec_ref_known(v_a_1636_, 2);
v___x_1656_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1638_, v_a_1640_, v_a_1642_, v_a_1644_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = 0;
v___x_1659_ = l_Lean_mkCIdentFrom(v_id_1633_, v_head_1654_, v___x_1658_);
v___x_1660_ = lean_box(v_symm_1632_);
lean_inc_ref(v_x_1631_);
v___x_1661_ = lean_apply_2(v_x_1631_, v___x_1660_, v___x_1659_);
v___x_1662_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_1661_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_dec(v_a_1657_);
lean_dec(v_tail_1655_);
lean_dec_ref(v_hint_1635_);
lean_dec(v_declName_1634_);
lean_dec_ref(v_x_1631_);
return v___x_1662_;
}
else
{
lean_object* v_a_1663_; uint8_t v___y_1665_; uint8_t v___x_1668_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
v___x_1668_ = l_Lean_Exception_isInterrupt(v_a_1663_);
if (v___x_1668_ == 0)
{
uint8_t v___x_1669_; 
v___x_1669_ = l_Lean_Exception_isRuntime(v_a_1663_);
v___y_1665_ = v___x_1669_;
goto v___jp_1664_;
}
else
{
lean_dec(v_a_1663_);
v___y_1665_ = v___x_1668_;
goto v___jp_1664_;
}
v___jp_1664_:
{
if (v___y_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref_known(v___x_1662_, 1);
v___x_1666_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1657_, v___y_1665_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_dec_ref_known(v___x_1666_, 1);
v_a_1636_ = v_tail_1655_;
goto _start;
}
else
{
lean_dec(v_tail_1655_);
lean_dec_ref(v_hint_1635_);
lean_dec(v_declName_1634_);
lean_dec_ref(v_x_1631_);
return v___x_1666_;
}
}
else
{
lean_dec(v_a_1657_);
lean_dec(v_tail_1655_);
lean_dec_ref(v_hint_1635_);
lean_dec(v_declName_1634_);
lean_dec_ref(v_x_1631_);
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_tail_1655_);
lean_dec(v_head_1654_);
lean_dec_ref(v_hint_1635_);
lean_dec(v_declName_1634_);
lean_dec_ref(v_x_1631_);
v_a_1670_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1656_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1656_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* v_x_1678_, lean_object* v_symm_1679_, lean_object* v_id_1680_, lean_object* v_declName_1681_, lean_object* v_hint_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
uint8_t v_symm_boxed_1693_; lean_object* v_res_1694_; 
v_symm_boxed_1693_ = lean_unbox(v_symm_1679_);
v_res_1694_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_1678_, v_symm_boxed_1693_, v_id_1680_, v_declName_1681_, v_hint_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_id_1680_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* v_a_1695_, lean_object* v_trees_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
v___x_1706_ = lean_apply_9(v_a_1695_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, lean_box(0));
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_a_1707_);
lean_ctor_set(v___x_1711_, 1, v_trees_1696_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v_trees_1696_);
v_a_1716_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1706_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1706_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* v_a_1724_, lean_object* v_trees_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(v_a_1724_, v_trees_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object* v___x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1736_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(lean_object* v___x_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(v___x_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(lean_object* v___y_1758_, lean_object* v_mkInfoTree_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v_a_1767_, lean_object* v_a_x3f_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v_infoState_1771_; lean_object* v_trees_1772_; lean_object* v___x_1773_; 
v___x_1770_ = lean_st_ref_get(v___y_1758_);
v_infoState_1771_ = lean_ctor_get(v___x_1770_, 7);
lean_inc_ref(v_infoState_1771_);
lean_dec(v___x_1770_);
v_trees_1772_ = lean_ctor_get(v_infoState_1771_, 2);
lean_inc_ref(v_trees_1772_);
lean_dec_ref(v_infoState_1771_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
v___x_1773_ = lean_apply_10(v_mkInfoTree_1759_, v_trees_1772_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1758_, lean_box(0));
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1812_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1812_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1812_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v_infoState_1779_; lean_object* v_env_1780_; lean_object* v_nextMacroScope_1781_; lean_object* v_ngen_1782_; lean_object* v_auxDeclNGen_1783_; lean_object* v_traceState_1784_; lean_object* v_cache_1785_; lean_object* v_messages_1786_; lean_object* v_snapshotTasks_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1811_; 
v___x_1778_ = lean_st_ref_take(v___y_1758_);
v_infoState_1779_ = lean_ctor_get(v___x_1778_, 7);
v_env_1780_ = lean_ctor_get(v___x_1778_, 0);
v_nextMacroScope_1781_ = lean_ctor_get(v___x_1778_, 1);
v_ngen_1782_ = lean_ctor_get(v___x_1778_, 2);
v_auxDeclNGen_1783_ = lean_ctor_get(v___x_1778_, 3);
v_traceState_1784_ = lean_ctor_get(v___x_1778_, 4);
v_cache_1785_ = lean_ctor_get(v___x_1778_, 5);
v_messages_1786_ = lean_ctor_get(v___x_1778_, 6);
v_snapshotTasks_1787_ = lean_ctor_get(v___x_1778_, 8);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1789_ = v___x_1778_;
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_snapshotTasks_1787_);
lean_inc(v_infoState_1779_);
lean_inc(v_messages_1786_);
lean_inc(v_cache_1785_);
lean_inc(v_traceState_1784_);
lean_inc(v_auxDeclNGen_1783_);
lean_inc(v_ngen_1782_);
lean_inc(v_nextMacroScope_1781_);
lean_inc(v_env_1780_);
lean_dec(v___x_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
uint8_t v_enabled_1791_; lean_object* v_assignment_1792_; lean_object* v_lazyAssignment_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1809_; 
v_enabled_1791_ = lean_ctor_get_uint8(v_infoState_1779_, sizeof(void*)*3);
v_assignment_1792_ = lean_ctor_get(v_infoState_1779_, 0);
v_lazyAssignment_1793_ = lean_ctor_get(v_infoState_1779_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_infoState_1779_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_infoState_1779_, 2);
lean_dec(v_unused_1810_);
v___x_1795_ = v_infoState_1779_;
v_isShared_1796_ = v_isSharedCheck_1809_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_lazyAssignment_1793_);
lean_inc(v_assignment_1792_);
lean_dec(v_infoState_1779_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1809_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = l_Lean_PersistentArray_push___redArg(v_a_1767_, v_a_1774_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 2, v___x_1797_);
v___x_1799_ = v___x_1795_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_assignment_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_lazyAssignment_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v___x_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*3, v_enabled_1791_);
v___x_1799_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1801_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 7, v___x_1799_);
v___x_1801_ = v___x_1789_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_env_1780_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_nextMacroScope_1781_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_ngen_1782_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_auxDeclNGen_1783_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_traceState_1784_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_cache_1785_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_messages_1786_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_snapshotTasks_1787_);
v___x_1801_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = lean_st_ref_set(v___y_1758_, v___x_1801_);
v___x_1803_ = lean_box(0);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1803_);
v___x_1805_ = v___x_1776_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v_a_1767_);
v_a_1813_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1773_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1773_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(lean_object* v___y_1821_, lean_object* v_mkInfoTree_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v_a_1830_, lean_object* v_a_x3f_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1821_, v_mkInfoTree_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v_a_1830_, v_a_x3f_1831_);
lean_dec(v_a_x3f_1831_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1821_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(32u);
v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1837_ = ((size_t)5ULL);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_unsigned_to_nat(32u);
v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1839_);
v___x_1841_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0);
v___x_1842_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1840_);
lean_ctor_set(v___x_1842_, 2, v___x_1838_);
lean_ctor_set(v___x_1842_, 3, v___x_1838_);
lean_ctor_set_usize(v___x_1842_, 4, v___x_1837_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v_infoState_1846_; lean_object* v_trees_1847_; lean_object* v___x_1848_; lean_object* v_infoState_1849_; lean_object* v_env_1850_; lean_object* v_nextMacroScope_1851_; lean_object* v_ngen_1852_; lean_object* v_auxDeclNGen_1853_; lean_object* v_traceState_1854_; lean_object* v_cache_1855_; lean_object* v_messages_1856_; lean_object* v_snapshotTasks_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1878_; 
v___x_1845_ = lean_st_ref_get(v___y_1843_);
v_infoState_1846_ = lean_ctor_get(v___x_1845_, 7);
lean_inc_ref(v_infoState_1846_);
lean_dec(v___x_1845_);
v_trees_1847_ = lean_ctor_get(v_infoState_1846_, 2);
lean_inc_ref(v_trees_1847_);
lean_dec_ref(v_infoState_1846_);
v___x_1848_ = lean_st_ref_take(v___y_1843_);
v_infoState_1849_ = lean_ctor_get(v___x_1848_, 7);
v_env_1850_ = lean_ctor_get(v___x_1848_, 0);
v_nextMacroScope_1851_ = lean_ctor_get(v___x_1848_, 1);
v_ngen_1852_ = lean_ctor_get(v___x_1848_, 2);
v_auxDeclNGen_1853_ = lean_ctor_get(v___x_1848_, 3);
v_traceState_1854_ = lean_ctor_get(v___x_1848_, 4);
v_cache_1855_ = lean_ctor_get(v___x_1848_, 5);
v_messages_1856_ = lean_ctor_get(v___x_1848_, 6);
v_snapshotTasks_1857_ = lean_ctor_get(v___x_1848_, 8);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1859_ = v___x_1848_;
v_isShared_1860_ = v_isSharedCheck_1878_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_snapshotTasks_1857_);
lean_inc(v_infoState_1849_);
lean_inc(v_messages_1856_);
lean_inc(v_cache_1855_);
lean_inc(v_traceState_1854_);
lean_inc(v_auxDeclNGen_1853_);
lean_inc(v_ngen_1852_);
lean_inc(v_nextMacroScope_1851_);
lean_inc(v_env_1850_);
lean_dec(v___x_1848_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1878_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
uint8_t v_enabled_1861_; lean_object* v_assignment_1862_; lean_object* v_lazyAssignment_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1876_; 
v_enabled_1861_ = lean_ctor_get_uint8(v_infoState_1849_, sizeof(void*)*3);
v_assignment_1862_ = lean_ctor_get(v_infoState_1849_, 0);
v_lazyAssignment_1863_ = lean_ctor_get(v_infoState_1849_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_infoState_1849_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v_infoState_1849_, 2);
lean_dec(v_unused_1877_);
v___x_1865_ = v_infoState_1849_;
v_isShared_1866_ = v_isSharedCheck_1876_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_lazyAssignment_1863_);
lean_inc(v_assignment_1862_);
lean_dec(v_infoState_1849_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1876_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 2, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_assignment_1862_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_lazyAssignment_1863_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v___x_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1875_, sizeof(void*)*3, v_enabled_1861_);
v___x_1869_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 7, v___x_1869_);
v___x_1871_ = v___x_1859_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_env_1850_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_nextMacroScope_1851_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_ngen_1852_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_auxDeclNGen_1853_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_traceState_1854_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v_cache_1855_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_messages_1856_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_snapshotTasks_1857_);
v___x_1871_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_st_ref_set(v___y_1843_, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_trees_1847_);
return v___x_1873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1879_);
lean_dec(v___y_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object* v_x_1882_, lean_object* v_mkInfoTree_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v_infoState_1894_; uint8_t v_enabled_1895_; 
v___x_1893_ = lean_st_ref_get(v___y_1891_);
v_infoState_1894_ = lean_ctor_get(v___x_1893_, 7);
lean_inc_ref(v_infoState_1894_);
lean_dec(v___x_1893_);
v_enabled_1895_ = lean_ctor_get_uint8(v_infoState_1894_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1894_);
if (v_enabled_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref(v_mkInfoTree_1883_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
v___x_1896_ = lean_apply_9(v_x_1882_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, lean_box(0));
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v_a_1898_; lean_object* v_r_1899_; 
v___x_1897_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_1891_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
v_r_1899_ = lean_apply_9(v_x_1882_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, lean_box(0));
if (lean_obj_tag(v_r_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1924_; 
v_a_1900_ = lean_ctor_get(v_r_1899_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_r_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1902_ = v_r_1899_;
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v_r_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
lean_inc(v_a_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 1);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1891_, v_mkInfoTree_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v_a_1898_, v___x_1905_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1906_, 0);
lean_dec(v_unused_1914_);
v___x_1908_ = v___x_1906_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_dec(v___x_1906_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_a_1900_);
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1900_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1900_);
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1925_ = lean_ctor_get(v_r_1899_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v_r_1899_, 1);
v___x_1926_ = lean_box(0);
v___x_1927_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_1891_, v_mkInfoTree_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v_a_1898_, v___x_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1927_, 0);
lean_dec(v_unused_1935_);
v___x_1929_ = v___x_1927_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_dec(v___x_1927_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 1);
lean_ctor_set(v___x_1929_, 0, v_a_1925_);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1925_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1925_);
v_a_1936_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1927_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1927_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object* v_x_1944_, lean_object* v_mkInfoTree_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_1944_, v_mkInfoTree_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(lean_object* v___x_1965_, uint8_t v___x_1966_, lean_object* v___x_1967_, lean_object* v_x_1968_, uint8_t v___y_1969_, lean_object* v___x_1970_, lean_object* v___x_1971_, lean_object* v___f_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_fileName_1982_; lean_object* v_fileMap_1983_; lean_object* v_options_1984_; lean_object* v_currRecDepth_1985_; lean_object* v_maxRecDepth_1986_; lean_object* v_ref_1987_; lean_object* v_currNamespace_1988_; lean_object* v_openDecls_1989_; lean_object* v_initHeartbeats_1990_; lean_object* v_maxHeartbeats_1991_; lean_object* v_quotContext_1992_; lean_object* v_currMacroScope_1993_; uint8_t v_diag_1994_; lean_object* v_cancelTk_x3f_1995_; uint8_t v_suppressElabErrors_1996_; lean_object* v_inheritedTraceOptions_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2015_; 
v_fileName_1982_ = lean_ctor_get(v___y_1979_, 0);
v_fileMap_1983_ = lean_ctor_get(v___y_1979_, 1);
v_options_1984_ = lean_ctor_get(v___y_1979_, 2);
v_currRecDepth_1985_ = lean_ctor_get(v___y_1979_, 3);
v_maxRecDepth_1986_ = lean_ctor_get(v___y_1979_, 4);
v_ref_1987_ = lean_ctor_get(v___y_1979_, 5);
v_currNamespace_1988_ = lean_ctor_get(v___y_1979_, 6);
v_openDecls_1989_ = lean_ctor_get(v___y_1979_, 7);
v_initHeartbeats_1990_ = lean_ctor_get(v___y_1979_, 8);
v_maxHeartbeats_1991_ = lean_ctor_get(v___y_1979_, 9);
v_quotContext_1992_ = lean_ctor_get(v___y_1979_, 10);
v_currMacroScope_1993_ = lean_ctor_get(v___y_1979_, 11);
v_diag_1994_ = lean_ctor_get_uint8(v___y_1979_, sizeof(void*)*14);
v_cancelTk_x3f_1995_ = lean_ctor_get(v___y_1979_, 12);
v_suppressElabErrors_1996_ = lean_ctor_get_uint8(v___y_1979_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1997_ = lean_ctor_get(v___y_1979_, 13);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___y_1979_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1999_ = v___y_1979_;
v_isShared_2000_ = v_isSharedCheck_2015_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_inheritedTraceOptions_1997_);
lean_inc(v_cancelTk_x3f_1995_);
lean_inc(v_currMacroScope_1993_);
lean_inc(v_quotContext_1992_);
lean_inc(v_maxHeartbeats_1991_);
lean_inc(v_initHeartbeats_1990_);
lean_inc(v_openDecls_1989_);
lean_inc(v_currNamespace_1988_);
lean_inc(v_ref_1987_);
lean_inc(v_maxRecDepth_1986_);
lean_inc(v_currRecDepth_1985_);
lean_inc(v_options_1984_);
lean_inc(v_fileMap_1983_);
lean_inc(v_fileName_1982_);
lean_dec(v___y_1979_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2015_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_ref_2001_; lean_object* v___x_2003_; 
v_ref_2001_ = l_Lean_replaceRef(v___x_1965_, v_ref_1987_);
lean_dec(v_ref_1987_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 5, v_ref_2001_);
v___x_2003_ = v___x_1999_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_fileName_1982_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_fileMap_1983_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_options_1984_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_currRecDepth_1985_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_maxRecDepth_1986_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_ref_2001_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_currNamespace_1988_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_openDecls_1989_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_initHeartbeats_1990_);
lean_ctor_set(v_reuseFailAlloc_2014_, 9, v_maxHeartbeats_1991_);
lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_quotContext_1992_);
lean_ctor_set(v_reuseFailAlloc_2014_, 11, v_currMacroScope_1993_);
lean_ctor_set(v_reuseFailAlloc_2014_, 12, v_cancelTk_x3f_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 13, v_inheritedTraceOptions_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*14, v_diag_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*14 + 1, v_suppressElabErrors_1996_);
v___x_2003_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
if (v___x_1966_ == 0)
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4));
lean_inc(v___x_1967_);
v___x_2005_ = l_Lean_Syntax_isOfKind(v___x_1967_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec_ref(v___f_1972_);
v___x_2006_ = lean_box(v___y_1969_);
v___x_2007_ = lean_apply_11(v_x_1968_, v___x_2006_, v___x_1967_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___x_2003_, v___y_1980_, lean_box(0));
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = l_Lean_Syntax_getArg(v___x_1967_, v___x_1970_);
lean_inc(v___x_2008_);
v___x_2009_ = l_Lean_Syntax_isOfKind(v___x_2008_, v___x_1971_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_dec(v___x_2008_);
lean_dec_ref(v___f_1972_);
v___x_2010_ = lean_box(v___y_1969_);
v___x_2011_ = lean_apply_11(v_x_1968_, v___x_2010_, v___x_1967_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___x_2003_, v___y_1980_, lean_box(0));
return v___x_2011_;
}
else
{
lean_object* v___x_2012_; 
lean_dec_ref(v_x_1968_);
lean_dec(v___x_1967_);
v___x_2012_ = lean_apply_10(v___f_1972_, v___x_2008_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___x_2003_, v___y_1980_, lean_box(0));
return v___x_2012_;
}
}
}
else
{
lean_object* v___x_2013_; 
lean_dec_ref(v_x_1968_);
v___x_2013_ = lean_apply_10(v___f_1972_, v___x_1967_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___x_2003_, v___y_1980_, lean_box(0));
return v___x_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2016_ = _args[0];
lean_object* v___x_2017_ = _args[1];
lean_object* v___x_2018_ = _args[2];
lean_object* v_x_2019_ = _args[3];
lean_object* v___y_2020_ = _args[4];
lean_object* v___x_2021_ = _args[5];
lean_object* v___x_2022_ = _args[6];
lean_object* v___f_2023_ = _args[7];
lean_object* v___y_2024_ = _args[8];
lean_object* v___y_2025_ = _args[9];
lean_object* v___y_2026_ = _args[10];
lean_object* v___y_2027_ = _args[11];
lean_object* v___y_2028_ = _args[12];
lean_object* v___y_2029_ = _args[13];
lean_object* v___y_2030_ = _args[14];
lean_object* v___y_2031_ = _args[15];
lean_object* v___y_2032_ = _args[16];
_start:
{
uint8_t v___x_16685__boxed_2033_; uint8_t v___y_16687__boxed_2034_; lean_object* v_res_2035_; 
v___x_16685__boxed_2033_ = lean_unbox(v___x_2017_);
v___y_16687__boxed_2034_ = lean_unbox(v___y_2020_);
v_res_2035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(v___x_2016_, v___x_16685__boxed_2033_, v___x_2018_, v_x_2019_, v___y_16687__boxed_2034_, v___x_2021_, v___x_2022_, v___f_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___x_2022_);
lean_dec(v___x_2021_);
lean_dec(v___x_2016_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(lean_object* v_a_2036_, lean_object* v_trees_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc_ref(v___y_2038_);
v___x_2047_ = lean_apply_9(v_a_2036_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, lean_box(0));
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2056_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_a_2048_);
lean_ctor_set(v___x_2052_, 1, v_trees_2037_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v_trees_2037_);
v_a_2057_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2047_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2047_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(lean_object* v_a_2065_, lean_object* v_trees_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(v_a_2065_, v_trees_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(lean_object* v_id_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Elab_Term_isLocalIdent_x3f(v_id_2077_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(lean_object* v_id_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(v_id_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2098_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(lean_object* v_x_2105_, uint8_t v___y_2106_, lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v_id_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___f_2119_; lean_object* v___x_2120_; 
lean_inc(v_id_2109_);
v___f_2119_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2119_, 0, v_id_2109_);
v___x_2120_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2119_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
if (lean_obj_tag(v_a_2121_) == 0)
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2111_, v___y_2113_, v___y_2115_, v___y_2117_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
lean_inc(v_id_2109_);
v___x_2124_ = l_Lean_realizeGlobalConstNoOverload(v_id_2109_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
lean_dec(v_a_2123_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc_n(v_a_2125_, 2);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = l_Lean_Meta_getEqnsFor_x3f(v_a_2125_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
if (lean_obj_tag(v_a_2127_) == 1)
{
lean_object* v_val_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v___x_2108_);
v_val_2128_ = lean_ctor_get(v_a_2127_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2130_ = v_a_2127_;
v_isShared_2131_ = v_isSharedCheck_2172_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_val_2128_);
lean_dec(v_a_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2172_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
uint8_t v___x_2132_; lean_object* v___y_2134_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2132_ = 0;
v___x_2161_ = lean_array_get_size(v_val_2128_);
v___x_2162_ = lean_nat_dec_eq(v___x_2161_, v___x_2107_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2163_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1);
v___x_2164_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_a_2125_);
v___x_2165_ = l_Lean_Name_str___override(v_a_2125_, v___x_2164_);
v___x_2166_ = l_Lean_MessageData_ofName(v___x_2165_);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2163_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_MessageData_hint_x27(v___x_2169_);
v___y_2134_ = v___x_2170_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
v___y_2134_ = v___x_2171_;
goto v___jp_2133_;
}
v___jp_2133_:
{
lean_object* v___x_2135_; 
lean_inc(v_a_2125_);
v___x_2135_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_a_2125_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v_lctx_2137_; lean_object* v___x_2139_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v_lctx_2137_ = lean_ctor_get(v___y_2114_, 2);
lean_inc_ref(v_lctx_2137_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v_lctx_2137_);
v___x_2139_ = v___x_2130_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_lctx_2137_);
v___x_2139_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_box(0);
lean_inc(v_id_2109_);
v___x_2141_ = l_Lean_Elab_Term_addTermInfo(v_id_2109_, v_a_2136_, v_a_2121_, v___x_2139_, v___x_2140_, v___x_2132_, v___x_2132_, v___x_2132_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref_known(v___x_2141_, 1);
v___x_2142_ = lean_array_to_list(v_val_2128_);
v___x_2143_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(v_x_2105_, v___y_2106_, v_id_2109_, v_a_2125_, v___y_2134_, v___x_2142_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v_id_2109_);
return v___x_2143_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___y_2134_);
lean_dec(v_val_2128_);
lean_dec(v_a_2125_);
lean_dec(v_id_2109_);
lean_dec_ref(v_x_2105_);
v_a_2144_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2141_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2141_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v___y_2134_);
lean_del_object(v___x_2130_);
lean_dec(v_val_2128_);
lean_dec(v_a_2125_);
lean_dec(v_id_2109_);
lean_dec_ref(v_x_2105_);
v_a_2153_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2135_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2135_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec(v_a_2127_);
lean_dec(v_a_2125_);
lean_dec(v_id_2109_);
v___x_2173_ = lean_box(v___y_2106_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
v___x_2174_ = lean_apply_11(v_x_2105_, v___x_2173_, v___x_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, lean_box(0));
return v___x_2174_;
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2125_);
lean_dec(v_id_2109_);
lean_dec(v___x_2108_);
lean_dec_ref(v_x_2105_);
v_a_2175_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2126_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2126_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_id_2109_);
v_a_2183_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2185_ = v___x_2124_;
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2124_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
uint8_t v___y_2188_; uint8_t v___x_2195_; 
v___x_2195_ = l_Lean_Exception_isInterrupt(v_a_2183_);
if (v___x_2195_ == 0)
{
uint8_t v___x_2196_; 
lean_inc(v_a_2183_);
v___x_2196_ = l_Lean_Exception_isRuntime(v_a_2183_);
v___y_2188_ = v___x_2196_;
goto v___jp_2187_;
}
else
{
v___y_2188_ = v___x_2195_;
goto v___jp_2187_;
}
v___jp_2187_:
{
if (v___y_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_del_object(v___x_2185_);
lean_dec(v_a_2183_);
v___x_2189_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2123_, v___y_2188_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref_known(v___x_2189_, 1);
v___x_2190_ = lean_box(v___y_2106_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
v___x_2191_ = lean_apply_11(v_x_2105_, v___x_2190_, v___x_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, lean_box(0));
return v___x_2191_;
}
else
{
lean_dec(v___x_2108_);
lean_dec_ref(v_x_2105_);
return v___x_2189_;
}
}
else
{
lean_object* v___x_2193_; 
lean_dec(v_a_2123_);
lean_dec(v___x_2108_);
lean_dec_ref(v_x_2105_);
if (v_isShared_2186_ == 0)
{
v___x_2193_ = v___x_2185_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2183_);
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
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_id_2109_);
lean_dec(v___x_2108_);
lean_dec_ref(v_x_2105_);
v_a_2198_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2122_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2122_);
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
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref_known(v_a_2121_, 1);
lean_dec(v_id_2109_);
v___x_2206_ = lean_box(v___y_2106_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
v___x_2207_ = lean_apply_11(v_x_2105_, v___x_2206_, v___x_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, lean_box(0));
return v___x_2207_;
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_id_2109_);
lean_dec(v___x_2108_);
lean_dec_ref(v_x_2105_);
v_a_2208_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2120_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2120_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___x_2218_, lean_object* v___x_2219_, lean_object* v_id_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v___y_16885__boxed_2230_; lean_object* v_res_2231_; 
v___y_16885__boxed_2230_ = lean_unbox(v___y_2217_);
v_res_2231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(v_x_2216_, v___y_16885__boxed_2230_, v___x_2218_, v___x_2219_, v_id_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___x_2218_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(lean_object* v_upperBound_2238_, lean_object* v_rules_2239_, lean_object* v_x_2240_, lean_object* v_a_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_nat_dec_lt(v_a_2241_, v_upperBound_2238_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_a_2241_);
lean_dec_ref(v_x_2240_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_b_2242_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___y_2262_; uint8_t v___y_2263_; lean_object* v___y_2287_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2254_ = lean_unsigned_to_nat(2u);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = lean_nat_mul(v_a_2241_, v___x_2254_);
v___x_2260_ = lean_array_get_borrowed(v___x_2255_, v_rules_2239_, v___x_2259_);
v___x_2297_ = lean_nat_add(v___x_2259_, v___x_2256_);
lean_dec(v___x_2259_);
v___x_2298_ = lean_array_get_size(v_rules_2239_);
v___x_2299_ = lean_nat_dec_lt(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_dec(v___x_2297_);
v___y_2287_ = v___x_2255_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_array_fget_borrowed(v_rules_2239_, v___x_2297_);
lean_dec(v___x_2297_);
lean_inc(v___x_2300_);
v___y_2287_ = v___x_2300_;
goto v___jp_2286_;
}
v___jp_2261_:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___y_2262_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___f_2266_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2266_, 0, v_a_2265_);
v___x_2267_ = l_Lean_Syntax_getArg(v___x_2260_, v___x_2256_);
v___x_2268_ = lean_box(v___y_2263_);
lean_inc_n(v___x_2267_, 2);
lean_inc_ref_n(v_x_2240_, 2);
v___f_2269_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2269_, 0, v_x_2240_);
lean_closure_set(v___f_2269_, 1, v___x_2268_);
lean_closure_set(v___f_2269_, 2, v___x_2256_);
lean_closure_set(v___f_2269_, 3, v___x_2267_);
v___x_2270_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1));
v___x_2271_ = l_Lean_Syntax_isOfKind(v___x_2267_, v___x_2270_);
v___x_2272_ = lean_box(v___x_2271_);
v___x_2273_ = lean_box(v___y_2263_);
lean_inc(v___x_2260_);
v___f_2274_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed), 17, 8);
lean_closure_set(v___f_2274_, 0, v___x_2260_);
lean_closure_set(v___f_2274_, 1, v___x_2272_);
lean_closure_set(v___f_2274_, 2, v___x_2267_);
lean_closure_set(v___f_2274_, 3, v_x_2240_);
lean_closure_set(v___f_2274_, 4, v___x_2273_);
lean_closure_set(v___f_2274_, 5, v___x_2256_);
lean_closure_set(v___f_2274_, 6, v___x_2270_);
lean_closure_set(v___f_2274_, 7, v___f_2269_);
v___x_2275_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2274_, v___f_2266_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; 
lean_dec_ref_known(v___x_2275_, 1);
v___x_2276_ = lean_nat_add(v_a_2241_, v___x_2256_);
lean_dec(v_a_2241_);
v_a_2241_ = v___x_2276_;
v_b_2242_ = v___x_2257_;
goto _start;
}
else
{
lean_dec(v_a_2241_);
lean_dec_ref(v_x_2240_);
return v___x_2275_;
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2241_);
lean_dec_ref(v_x_2240_);
v_a_2278_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2264_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2264_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2288_ = lean_mk_empty_array_with_capacity(v___x_2254_);
lean_inc(v___x_2260_);
v___x_2289_ = lean_array_push(v___x_2288_, v___x_2260_);
v___x_2290_ = lean_array_push(v___x_2289_, v___y_2287_);
v___x_2291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2292_ = lean_box(2);
v___x_2293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___x_2291_);
lean_ctor_set(v___x_2293_, 2, v___x_2290_);
v___x_2294_ = l_Lean_Syntax_getArg(v___x_2260_, v___x_2258_);
v___x_2295_ = l_Lean_Syntax_isNone(v___x_2294_);
lean_dec(v___x_2294_);
if (v___x_2295_ == 0)
{
v___y_2262_ = v___x_2293_;
v___y_2263_ = v___x_2252_;
goto v___jp_2261_;
}
else
{
uint8_t v___x_2296_; 
v___x_2296_ = 0;
v___y_2262_ = v___x_2293_;
v___y_2263_ = v___x_2296_;
goto v___jp_2261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(lean_object* v_upperBound_2301_, lean_object* v_rules_2302_, lean_object* v_x_2303_, lean_object* v_a_2304_, lean_object* v_b_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2301_, v_rules_2302_, v_x_2303_, v_a_2304_, v_b_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v_rules_2302_);
lean_dec(v_upperBound_2301_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* v_token_2318_, lean_object* v_rwRulesSeqStx_2319_, lean_object* v_x_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; lean_object* v_lbrak_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2330_ = lean_unsigned_to_nat(0u);
v_lbrak_2331_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2319_, v___x_2330_);
v___x_2332_ = lean_unsigned_to_nat(2u);
v___x_2333_ = lean_mk_empty_array_with_capacity(v___x_2332_);
v___x_2334_ = lean_array_push(v___x_2333_, v_token_2318_);
v___x_2335_ = lean_array_push(v___x_2334_, v_lbrak_2331_);
v___x_2336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3));
v___x_2337_ = lean_box(2);
v___x_2338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
lean_ctor_set(v___x_2338_, 2, v___x_2335_);
v___x_2339_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2338_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2341_, 0, v_a_2340_);
v___x_2342_ = lean_box(0);
v___f_2343_ = ((lean_object*)(l_Lean_Elab_Tactic_withRWRulesSeq___closed__0));
v___x_2344_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_2343_, v___f_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_rules_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec_ref_known(v___x_2344_, 1);
v___x_2345_ = lean_unsigned_to_nat(1u);
v___x_2346_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_2319_, v___x_2345_);
v_rules_2347_ = l_Lean_Syntax_getArgs(v___x_2346_);
lean_dec(v___x_2346_);
v___x_2348_ = lean_array_get_size(v_rules_2347_);
v___x_2349_ = lean_nat_add(v___x_2348_, v___x_2345_);
v___x_2350_ = lean_nat_shiftr(v___x_2349_, v___x_2345_);
lean_dec(v___x_2349_);
v___x_2351_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v___x_2350_, v_rules_2347_, v_x_2320_, v___x_2330_, v___x_2342_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec_ref(v_rules_2347_);
lean_dec(v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2351_, 0);
lean_dec(v_unused_2359_);
v___x_2353_ = v___x_2351_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v___x_2351_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2342_);
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2342_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
return v___x_2351_;
}
}
else
{
lean_dec_ref(v_x_2320_);
return v___x_2344_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_x_2320_);
v_a_2360_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2339_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2339_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* v_token_2368_, lean_object* v_rwRulesSeqStx_2369_, lean_object* v_x_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Elab_Tactic_withRWRulesSeq(v_token_2368_, v_rwRulesSeqStx_2369_, v_x_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_rwRulesSeqStx_2369_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object* v_00_u03b1_2401_, lean_object* v_x_2402_, lean_object* v_mkInfoTree_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v_x_2402_, v_mkInfoTree_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_x_2415_, lean_object* v_mkInfoTree_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(v_00_u03b1_2414_, v_x_2415_, v_mkInfoTree_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(lean_object* v_upperBound_2427_, lean_object* v_rules_2428_, lean_object* v_x_2429_, lean_object* v_inst_2430_, lean_object* v_R_2431_, lean_object* v_a_2432_, lean_object* v_b_2433_, lean_object* v_c_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v_upperBound_2427_, v_rules_2428_, v_x_2429_, v_a_2432_, v_b_2433_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2445_ = _args[0];
lean_object* v_rules_2446_ = _args[1];
lean_object* v_x_2447_ = _args[2];
lean_object* v_inst_2448_ = _args[3];
lean_object* v_R_2449_ = _args[4];
lean_object* v_a_2450_ = _args[5];
lean_object* v_b_2451_ = _args[6];
lean_object* v_c_2452_ = _args[7];
lean_object* v___y_2453_ = _args[8];
lean_object* v___y_2454_ = _args[9];
lean_object* v___y_2455_ = _args[10];
lean_object* v___y_2456_ = _args[11];
lean_object* v___y_2457_ = _args[12];
lean_object* v___y_2458_ = _args[13];
lean_object* v___y_2459_ = _args[14];
lean_object* v___y_2460_ = _args[15];
lean_object* v___y_2461_ = _args[16];
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(v_upperBound_2445_, v_rules_2446_, v_x_2447_, v_inst_2448_, v_R_2449_, v_a_2450_, v_b_2451_, v_c_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v_rules_2446_);
lean_dec(v_upperBound_2445_);
return v_res_2462_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_box(0);
v___x_2464_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set(v___x_2465_, 1, v___x_2463_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_ref_2491_; lean_object* v___x_2492_; lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2501_; 
v_ref_2491_ = lean_ctor_get(v___y_2488_, 5);
v___x_2492_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_inc(v_ref_2491_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_ref_2491_);
lean_ctor_set(v___x_2497_, 1, v_a_2493_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
lean_ctor_set(v___x_2495_, 0, v___x_2497_);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2508_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(lean_object* v_ctor_2513_, lean_object* v_args_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_2582_ = lean_string_dec_eq(v_ctor_2513_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_2583_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = lean_array_get_size(v_args_2514_);
v___x_2585_ = lean_unsigned_to_nat(4u);
v___x_2586_ = lean_nat_dec_eq(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v___x_2587_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_2588_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2587_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
else
{
goto v___jp_2520_;
}
}
v___jp_2520_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2521_ = l_Lean_instInhabitedExpr;
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_borrowed(v___x_2521_, v_args_2514_, v___x_2522_);
lean_inc(v___x_2523_);
v___x_2524_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v___x_2523_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_array_get_borrowed(v___x_2521_, v_args_2514_, v___x_2526_);
lean_inc(v___x_2527_);
v___x_2528_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2527_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_unsigned_to_nat(2u);
v___x_2531_ = lean_array_get_borrowed(v___x_2521_, v_args_2514_, v___x_2530_);
lean_inc(v___x_2531_);
v___x_2532_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v___x_2531_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = lean_unsigned_to_nat(3u);
v___x_2535_ = lean_array_get_borrowed(v___x_2521_, v_args_2514_, v___x_2534_);
lean_inc(v___x_2535_);
v___x_2536_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v___x_2535_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2548_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; uint8_t v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2546_; 
v___x_2541_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2541_, 0, v_a_2533_);
v___x_2542_ = lean_unbox(v_a_2525_);
lean_dec(v_a_2525_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*1, v___x_2542_);
v___x_2543_ = lean_unbox(v_a_2529_);
lean_dec(v_a_2529_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*1 + 1, v___x_2543_);
v___x_2544_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*1 + 2, v___x_2544_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2541_);
v___x_2546_ = v___x_2539_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_a_2533_);
lean_dec(v_a_2529_);
lean_dec(v_a_2525_);
v_a_2549_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2536_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2536_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_a_2529_);
lean_dec(v_a_2525_);
v_a_2557_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2532_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2532_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_a_2525_);
v_a_2565_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2528_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2528_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2524_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2524_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_2597_, lean_object* v_args_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v_ctor_2597_, v_args_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v_args_2598_);
lean_dec_ref(v_ctor_2597_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v___f_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___f_2620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0));
v___x_2621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2622_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2621_, v___f_2620_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_2630_, lean_object* v_msg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_msg_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_2638_, v_msg_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2645_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = lean_box(0);
v___x_2648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_2649_ = l_Lean_Expr_const___override(v___x_2648_, v___x_2647_);
return v___x_2649_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_2653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0));
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___x_2652_);
return v___x_2654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig(void){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
return v___x_2655_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_box(1);
v___x_2657_ = l_Lean_MessageData_ofFormat(v___x_2656_);
return v___x_2657_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2));
v___x_2662_ = l_Lean_MessageData_ofFormat(v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(lean_object* v_x_2663_, lean_object* v_x_2664_){
_start:
{
if (lean_obj_tag(v_x_2664_) == 0)
{
return v_x_2663_;
}
else
{
lean_object* v_head_2665_; lean_object* v_tail_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2688_; 
v_head_2665_ = lean_ctor_get(v_x_2664_, 0);
v_tail_2666_ = lean_ctor_get(v_x_2664_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2668_ = v_x_2664_;
v_isShared_2669_ = v_isSharedCheck_2688_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_tail_2666_);
lean_inc(v_head_2665_);
lean_dec(v_x_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2688_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_before_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2686_; 
v_before_2670_ = lean_ctor_get(v_head_2665_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_head_2665_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v_head_2665_, 1);
lean_dec(v_unused_2687_);
v___x_2672_ = v_head_2665_;
v_isShared_2673_ = v_isSharedCheck_2686_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_before_2670_);
lean_dec(v_head_2665_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2686_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 7);
lean_ctor_set(v___x_2672_, 1, v___x_2674_);
lean_ctor_set(v___x_2672_, 0, v_x_2663_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_x_2663_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 7);
lean_ctor_set(v___x_2668_, 1, v___x_2677_);
lean_ctor_set(v___x_2668_, 0, v___x_2676_);
v___x_2679_ = v___x_2668_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = l_Lean_MessageData_ofSyntax(v_before_2670_);
v___x_2681_ = l_Lean_indentD(v___x_2680_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2679_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v_x_2663_ = v___x_2682_;
v_x_2664_ = v_tail_2666_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(lean_object* v_opts_2689_, lean_object* v_opt_2690_){
_start:
{
lean_object* v_name_2691_; lean_object* v_defValue_2692_; lean_object* v_map_2693_; lean_object* v___x_2694_; 
v_name_2691_ = lean_ctor_get(v_opt_2690_, 0);
v_defValue_2692_ = lean_ctor_get(v_opt_2690_, 1);
v_map_2693_ = lean_ctor_get(v_opts_2689_, 0);
v___x_2694_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2693_, v_name_2691_);
if (lean_obj_tag(v___x_2694_) == 0)
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_unbox(v_defValue_2692_);
return v___x_2695_;
}
else
{
lean_object* v_val_2696_; 
v_val_2696_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v___x_2694_, 1);
if (lean_obj_tag(v_val_2696_) == 1)
{
uint8_t v_v_2697_; 
v_v_2697_ = lean_ctor_get_uint8(v_val_2696_, 0);
lean_dec_ref_known(v_val_2696_, 0);
return v_v_2697_;
}
else
{
uint8_t v___x_2698_; 
lean_dec(v_val_2696_);
v___x_2698_ = lean_unbox(v_defValue_2692_);
return v___x_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_opts_2699_, lean_object* v_opt_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_2699_, v_opt_2700_);
lean_dec_ref(v_opt_2700_);
lean_dec_ref(v_opts_2699_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1));
v___x_2707_ = l_Lean_MessageData_ofFormat(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(lean_object* v_msgData_2708_, lean_object* v_macroStack_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_options_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_options_2712_ = lean_ctor_get(v___y_2710_, 2);
v___x_2713_ = l_Lean_Elab_pp_macroStack;
v___x_2714_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_options_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; 
lean_dec(v_macroStack_2709_);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_msgData_2708_);
return v___x_2715_;
}
else
{
if (lean_obj_tag(v_macroStack_2709_) == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v_msgData_2708_);
return v___x_2716_;
}
else
{
lean_object* v_head_2717_; lean_object* v_after_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2733_; 
v_head_2717_ = lean_ctor_get(v_macroStack_2709_, 0);
lean_inc(v_head_2717_);
v_after_2718_ = lean_ctor_get(v_head_2717_, 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_head_2717_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v_head_2717_, 0);
lean_dec(v_unused_2734_);
v___x_2720_ = v_head_2717_;
v_isShared_2721_ = v_isSharedCheck_2733_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_after_2718_);
lean_dec(v_head_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2733_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 7);
lean_ctor_set(v___x_2720_, 1, v___x_2722_);
lean_ctor_set(v___x_2720_, 0, v_msgData_2708_);
v___x_2724_ = v___x_2720_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_msgData_2708_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_msgData_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2725_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l_Lean_MessageData_ofSyntax(v_after_2718_);
v___x_2728_ = l_Lean_indentD(v___x_2727_);
v_msgData_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2729_, 0, v___x_2726_);
lean_ctor_set(v_msgData_2729_, 1, v___x_2728_);
v___x_2730_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_2729_, v_macroStack_2709_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_msgData_2735_, lean_object* v_macroStack_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_2735_, v_macroStack_2736_, v___y_2737_);
lean_dec_ref(v___y_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(lean_object* v_msg_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_ref_2748_; lean_object* v___x_2749_; lean_object* v_a_2750_; lean_object* v_macroStack_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
v_ref_2748_ = lean_ctor_get(v___y_2745_, 5);
v___x_2749_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_2740_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
v_macroStack_2751_ = lean_ctor_get(v___y_2741_, 1);
v___x_2752_ = l_Lean_Elab_getBetterRef(v_ref_2748_, v_macroStack_2751_);
lean_inc(v_macroStack_2751_);
v___x_2753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_2750_, v_macroStack_2751_, v___y_2745_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2752_);
lean_ctor_set(v___x_2758_, 1, v_a_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 1);
lean_ctor_set(v___x_2756_, 0, v___x_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(lean_object* v_msg_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(lean_object* v_e_2772_, lean_object* v___y_2773_){
_start:
{
uint8_t v___x_2775_; 
v___x_2775_ = l_Lean_Expr_hasMVar(v_e_2772_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_e_2772_);
return v___x_2776_;
}
else
{
lean_object* v___x_2777_; lean_object* v_mctx_2778_; lean_object* v___x_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2782_; lean_object* v_cache_2783_; lean_object* v_zetaDeltaFVarIds_2784_; lean_object* v_postponed_2785_; lean_object* v_diag_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2795_; 
v___x_2777_ = lean_st_ref_get(v___y_2773_);
v_mctx_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_mctx_2778_);
lean_dec(v___x_2777_);
v___x_2779_ = l_Lean_instantiateMVarsCore(v_mctx_2778_, v_e_2772_);
v_fst_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_fst_2780_);
v_snd_2781_ = lean_ctor_get(v___x_2779_, 1);
lean_inc(v_snd_2781_);
lean_dec_ref(v___x_2779_);
v___x_2782_ = lean_st_ref_take(v___y_2773_);
v_cache_2783_ = lean_ctor_get(v___x_2782_, 1);
v_zetaDeltaFVarIds_2784_ = lean_ctor_get(v___x_2782_, 2);
v_postponed_2785_ = lean_ctor_get(v___x_2782_, 3);
v_diag_2786_ = lean_ctor_get(v___x_2782_, 4);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2782_, 0);
lean_dec(v_unused_2796_);
v___x_2788_ = v___x_2782_;
v_isShared_2789_ = v_isSharedCheck_2795_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_diag_2786_);
lean_inc(v_postponed_2785_);
lean_inc(v_zetaDeltaFVarIds_2784_);
lean_inc(v_cache_2783_);
lean_dec(v___x_2782_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2795_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v_snd_2781_);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_snd_2781_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_cache_2783_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_zetaDeltaFVarIds_2784_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_postponed_2785_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_diag_2786_);
v___x_2791_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_st_ref_set(v___y_2773_, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_fst_2780_);
return v___x_2793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(lean_object* v_e_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_2797_, v___y_2798_);
lean_dec(v___y_2798_);
return v_res_2800_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = l_Lean_Elab_abortTermExceptionId;
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___x_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg(){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v_res_2808_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = lean_box(0);
v___x_2815_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1));
v___x_2816_ = l_Lean_Expr_const___override(v___x_2815_, v___x_2814_);
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2817_; lean_object* v_ty_x3f_2818_; 
v___x_2817_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v_ty_x3f_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_2818_, 0, v___x_2817_);
return v_ty_x3f_2818_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4));
v___x_2821_ = l_Lean_stringToMessageData(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
v___x_2823_ = l_Lean_MessageData_ofExpr(v___x_2822_);
return v___x_2823_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
v___x_2825_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v___x_2824_);
return v___x_2826_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_2828_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2827_);
return v___x_2829_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11));
v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(lean_object* v_stx_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_ty_x3f_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v_fileName_2850_; lean_object* v_fileMap_2851_; lean_object* v_options_2852_; lean_object* v_currRecDepth_2853_; lean_object* v_maxRecDepth_2854_; lean_object* v_ref_2855_; lean_object* v_currNamespace_2856_; lean_object* v_openDecls_2857_; lean_object* v_initHeartbeats_2858_; lean_object* v_maxHeartbeats_2859_; lean_object* v_quotContext_2860_; lean_object* v_currMacroScope_2861_; uint8_t v_diag_2862_; lean_object* v_cancelTk_x3f_2863_; uint8_t v_suppressElabErrors_2864_; lean_object* v_inheritedTraceOptions_2865_; uint8_t v___x_2866_; lean_object* v_ref_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_ty_x3f_2844_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
v___x_2845_ = 1;
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_box(v___x_2845_);
v___x_2848_ = lean_box(v___x_2845_);
lean_inc(v_stx_2836_);
v___x_2849_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2849_, 0, v_stx_2836_);
lean_closure_set(v___x_2849_, 1, v_ty_x3f_2844_);
lean_closure_set(v___x_2849_, 2, v___x_2847_);
lean_closure_set(v___x_2849_, 3, v___x_2848_);
lean_closure_set(v___x_2849_, 4, v___x_2846_);
v_fileName_2850_ = lean_ctor_get(v_a_2841_, 0);
v_fileMap_2851_ = lean_ctor_get(v_a_2841_, 1);
v_options_2852_ = lean_ctor_get(v_a_2841_, 2);
v_currRecDepth_2853_ = lean_ctor_get(v_a_2841_, 3);
v_maxRecDepth_2854_ = lean_ctor_get(v_a_2841_, 4);
v_ref_2855_ = lean_ctor_get(v_a_2841_, 5);
v_currNamespace_2856_ = lean_ctor_get(v_a_2841_, 6);
v_openDecls_2857_ = lean_ctor_get(v_a_2841_, 7);
v_initHeartbeats_2858_ = lean_ctor_get(v_a_2841_, 8);
v_maxHeartbeats_2859_ = lean_ctor_get(v_a_2841_, 9);
v_quotContext_2860_ = lean_ctor_get(v_a_2841_, 10);
v_currMacroScope_2861_ = lean_ctor_get(v_a_2841_, 11);
v_diag_2862_ = lean_ctor_get_uint8(v_a_2841_, sizeof(void*)*14);
v_cancelTk_x3f_2863_ = lean_ctor_get(v_a_2841_, 12);
v_suppressElabErrors_2864_ = lean_ctor_get_uint8(v_a_2841_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2865_ = lean_ctor_get(v_a_2841_, 13);
v___x_2866_ = 1;
v_ref_2867_ = l_Lean_replaceRef(v_stx_2836_, v_ref_2855_);
lean_dec(v_stx_2836_);
lean_inc_ref(v_inheritedTraceOptions_2865_);
lean_inc(v_cancelTk_x3f_2863_);
lean_inc(v_currMacroScope_2861_);
lean_inc(v_quotContext_2860_);
lean_inc(v_maxHeartbeats_2859_);
lean_inc(v_initHeartbeats_2858_);
lean_inc(v_openDecls_2857_);
lean_inc(v_currNamespace_2856_);
lean_inc(v_maxRecDepth_2854_);
lean_inc(v_currRecDepth_2853_);
lean_inc_ref(v_options_2852_);
lean_inc_ref(v_fileMap_2851_);
lean_inc_ref(v_fileName_2850_);
v___x_2868_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2868_, 0, v_fileName_2850_);
lean_ctor_set(v___x_2868_, 1, v_fileMap_2851_);
lean_ctor_set(v___x_2868_, 2, v_options_2852_);
lean_ctor_set(v___x_2868_, 3, v_currRecDepth_2853_);
lean_ctor_set(v___x_2868_, 4, v_maxRecDepth_2854_);
lean_ctor_set(v___x_2868_, 5, v_ref_2867_);
lean_ctor_set(v___x_2868_, 6, v_currNamespace_2856_);
lean_ctor_set(v___x_2868_, 7, v_openDecls_2857_);
lean_ctor_set(v___x_2868_, 8, v_initHeartbeats_2858_);
lean_ctor_set(v___x_2868_, 9, v_maxHeartbeats_2859_);
lean_ctor_set(v___x_2868_, 10, v_quotContext_2860_);
lean_ctor_set(v___x_2868_, 11, v_currMacroScope_2861_);
lean_ctor_set(v___x_2868_, 12, v_cancelTk_x3f_2863_);
lean_ctor_set(v___x_2868_, 13, v_inheritedTraceOptions_2865_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*14, v_diag_2862_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*14 + 1, v_suppressElabErrors_2864_);
v___x_2869_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2849_, v___x_2866_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v___x_2868_, v_a_2842_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v_a_2872_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; uint8_t v___y_2883_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; uint8_t v___x_2967_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_2870_, v_a_2840_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v___x_2967_ = l_Lean_Expr_hasSorry(v_a_2872_);
if (v___x_2967_ == 0)
{
v___y_2912_ = v_a_2837_;
v___y_2913_ = v_a_2838_;
v___y_2914_ = v_a_2839_;
v___y_2915_ = v_a_2840_;
v___y_2916_ = v___x_2868_;
v___y_2917_ = v_a_2842_;
goto v___jp_2911_;
}
else
{
uint8_t v___x_2968_; 
v___x_2968_ = l_Lean_Expr_hasSyntheticSorry(v_a_2872_);
if (v___x_2968_ == 0)
{
v___y_2949_ = v_a_2837_;
v___y_2950_ = v_a_2838_;
v___y_2951_ = v_a_2839_;
v___y_2952_ = v_a_2840_;
v___y_2953_ = v___x_2868_;
v___y_2954_ = v_a_2842_;
goto v___jp_2948_;
}
else
{
lean_object* v___x_2969_; lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_a_2872_);
lean_dec_ref_known(v___x_2868_, 14);
v___x_2969_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
v___jp_2873_:
{
if (v___y_2883_ == 0)
{
if (lean_obj_tag(v___y_2879_) == 0)
{
lean_dec_ref_known(v___y_2879_, 2);
lean_dec_ref(v___y_2881_);
lean_dec(v_a_2872_);
return v___y_2876_;
}
else
{
lean_object* v_id_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2897_; 
v_id_2884_ = lean_ctor_get(v___y_2879_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___y_2879_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___y_2879_, 1);
lean_dec(v_unused_2898_);
v___x_2886_ = v___y_2879_;
v_isShared_2887_ = v_isSharedCheck_2897_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_id_2884_);
lean_dec(v___y_2879_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2897_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
uint8_t v___x_2888_; 
v___x_2888_ = l_Lean_instBEqInternalExceptionId_beq(v___y_2878_, v_id_2884_);
lean_dec(v_id_2884_);
if (v___x_2888_ == 0)
{
lean_del_object(v___x_2886_);
lean_dec_ref(v___y_2881_);
lean_dec(v_a_2872_);
return v___y_2876_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_dec_ref(v___y_2876_);
v___x_2889_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
v___x_2890_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_2891_ = l_Lean_indentExpr(v_a_2872_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set_tag(v___x_2886_, 7);
lean_ctor_set(v___x_2886_, 1, v___x_2891_);
lean_ctor_set(v___x_2886_, 0, v___x_2890_);
v___x_2893_ = v___x_2886_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
lean_ctor_set(v___x_2894_, 1, v___x_2889_);
v___x_2895_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_2894_, v___y_2882_, v___y_2874_, v___y_2877_, v___y_2875_, v___y_2881_, v___y_2880_);
lean_dec_ref(v___y_2881_);
return v___x_2895_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v_a_2872_);
return v___y_2876_;
}
}
v___jp_2899_:
{
lean_object* v___x_2906_; 
lean_inc(v_a_2872_);
v___x_2906_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_2872_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_dec_ref(v___y_2904_);
lean_dec(v_a_2872_);
return v___x_2906_;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
v___x_2908_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2909_ = l_Lean_Exception_isInterrupt(v_a_2907_);
if (v___x_2909_ == 0)
{
uint8_t v___x_2910_; 
lean_inc(v_a_2907_);
v___x_2910_ = l_Lean_Exception_isRuntime(v_a_2907_);
v___y_2874_ = v___y_2901_;
v___y_2875_ = v___y_2903_;
v___y_2876_ = v___x_2906_;
v___y_2877_ = v___y_2902_;
v___y_2878_ = v___x_2908_;
v___y_2879_ = v_a_2907_;
v___y_2880_ = v___y_2905_;
v___y_2881_ = v___y_2904_;
v___y_2882_ = v___y_2900_;
v___y_2883_ = v___x_2910_;
goto v___jp_2873_;
}
else
{
v___y_2874_ = v___y_2901_;
v___y_2875_ = v___y_2903_;
v___y_2876_ = v___x_2906_;
v___y_2877_ = v___y_2902_;
v___y_2878_ = v___x_2908_;
v___y_2879_ = v_a_2907_;
v___y_2880_ = v___y_2905_;
v___y_2881_ = v___y_2904_;
v___y_2882_ = v___y_2900_;
v___y_2883_ = v___x_2909_;
goto v___jp_2873_;
}
}
}
v___jp_2911_:
{
lean_object* v___x_2918_; 
lean_inc(v_a_2872_);
v___x_2918_ = l_Lean_Meta_getMVars(v_a_2872_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2920_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2919_, v___x_2846_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v_a_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; uint8_t v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = lean_unbox(v_a_2921_);
lean_dec(v_a_2921_);
if (v___x_2922_ == 0)
{
v___y_2900_ = v___y_2912_;
v___y_2901_ = v___y_2913_;
v___y_2902_ = v___y_2914_;
v___y_2903_ = v___y_2915_;
v___y_2904_ = v___y_2916_;
v___y_2905_ = v___y_2917_;
goto v___jp_2899_;
}
else
{
lean_object* v___x_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v___y_2916_);
lean_dec(v_a_2872_);
v___x_2923_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec_ref(v___y_2916_);
lean_dec(v_a_2872_);
v_a_2932_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2920_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2920_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec_ref(v___y_2916_);
lean_dec(v_a_2872_);
v_a_2940_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2918_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2918_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
v___jp_2948_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
v___x_2955_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_2956_ = l_Lean_indentExpr(v_a_2872_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_2957_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec_ref(v___y_2953_);
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref_known(v___x_2868_, 14);
v_a_2978_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2869_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2869_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_stx_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(lean_object* v_stx_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_fileName_3003_; lean_object* v_fileMap_3004_; lean_object* v_options_3005_; lean_object* v_currRecDepth_3006_; lean_object* v_maxRecDepth_3007_; lean_object* v_ref_3008_; lean_object* v_currNamespace_3009_; lean_object* v_openDecls_3010_; lean_object* v_initHeartbeats_3011_; lean_object* v_maxHeartbeats_3012_; lean_object* v_quotContext_3013_; lean_object* v_currMacroScope_3014_; uint8_t v_diag_3015_; lean_object* v_cancelTk_x3f_3016_; uint8_t v_suppressElabErrors_3017_; lean_object* v_inheritedTraceOptions_3018_; lean_object* v_ref_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_fileName_3003_ = lean_ctor_get(v_a_3000_, 0);
v_fileMap_3004_ = lean_ctor_get(v_a_3000_, 1);
v_options_3005_ = lean_ctor_get(v_a_3000_, 2);
v_currRecDepth_3006_ = lean_ctor_get(v_a_3000_, 3);
v_maxRecDepth_3007_ = lean_ctor_get(v_a_3000_, 4);
v_ref_3008_ = lean_ctor_get(v_a_3000_, 5);
v_currNamespace_3009_ = lean_ctor_get(v_a_3000_, 6);
v_openDecls_3010_ = lean_ctor_get(v_a_3000_, 7);
v_initHeartbeats_3011_ = lean_ctor_get(v_a_3000_, 8);
v_maxHeartbeats_3012_ = lean_ctor_get(v_a_3000_, 9);
v_quotContext_3013_ = lean_ctor_get(v_a_3000_, 10);
v_currMacroScope_3014_ = lean_ctor_get(v_a_3000_, 11);
v_diag_3015_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*14);
v_cancelTk_x3f_3016_ = lean_ctor_get(v_a_3000_, 12);
v_suppressElabErrors_3017_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3018_ = lean_ctor_get(v_a_3000_, 13);
v_ref_3019_ = l_Lean_replaceRef(v_stx_2995_, v_ref_3008_);
lean_inc_ref(v_inheritedTraceOptions_3018_);
lean_inc(v_cancelTk_x3f_3016_);
lean_inc(v_currMacroScope_3014_);
lean_inc(v_quotContext_3013_);
lean_inc(v_maxHeartbeats_3012_);
lean_inc(v_initHeartbeats_3011_);
lean_inc(v_openDecls_3010_);
lean_inc(v_currNamespace_3009_);
lean_inc(v_maxRecDepth_3007_);
lean_inc(v_currRecDepth_3006_);
lean_inc_ref(v_options_3005_);
lean_inc_ref(v_fileMap_3004_);
lean_inc_ref(v_fileName_3003_);
v___x_3020_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3020_, 0, v_fileName_3003_);
lean_ctor_set(v___x_3020_, 1, v_fileMap_3004_);
lean_ctor_set(v___x_3020_, 2, v_options_3005_);
lean_ctor_set(v___x_3020_, 3, v_currRecDepth_3006_);
lean_ctor_set(v___x_3020_, 4, v_maxRecDepth_3007_);
lean_ctor_set(v___x_3020_, 5, v_ref_3019_);
lean_ctor_set(v___x_3020_, 6, v_currNamespace_3009_);
lean_ctor_set(v___x_3020_, 7, v_openDecls_3010_);
lean_ctor_set(v___x_3020_, 8, v_initHeartbeats_3011_);
lean_ctor_set(v___x_3020_, 9, v_maxHeartbeats_3012_);
lean_ctor_set(v___x_3020_, 10, v_quotContext_3013_);
lean_ctor_set(v___x_3020_, 11, v_currMacroScope_3014_);
lean_ctor_set(v___x_3020_, 12, v_cancelTk_x3f_3016_);
lean_ctor_set(v___x_3020_, 13, v_inheritedTraceOptions_3018_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*14, v_diag_3015_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*14 + 1, v_suppressElabErrors_3017_);
lean_inc(v_stx_2995_);
v___x_3021_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_stx_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v___x_3020_, v_a_3001_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref_known(v___x_3020_, 14);
lean_dec(v_stx_2995_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3030_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3030_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_fst_3026_; lean_object* v___x_3028_; 
v_fst_3026_ = lean_ctor_get(v_a_3022_, 0);
lean_inc(v_fst_3026_);
lean_dec(v_a_3022_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v_fst_3026_);
v___x_3028_ = v___x_3024_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_fst_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3046_; 
v_a_3031_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3033_ = v___x_3021_;
v_isShared_3034_ = v_isSharedCheck_3046_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3021_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3046_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3035_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3031_);
if (v_isShared_3034_ == 0)
{
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3031_);
v___x_3037_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
uint8_t v___y_3039_; uint8_t v___x_3043_; 
v___x_3043_ = l_Lean_Exception_isInterrupt(v_a_3031_);
if (v___x_3043_ == 0)
{
uint8_t v___x_3044_; 
lean_inc(v_a_3031_);
v___x_3044_ = l_Lean_Exception_isRuntime(v_a_3031_);
v___y_3039_ = v___x_3044_;
goto v___jp_3038_;
}
else
{
v___y_3039_ = v___x_3043_;
goto v___jp_3038_;
}
v___jp_3038_:
{
if (v___y_3039_ == 0)
{
if (lean_obj_tag(v_a_3031_) == 0)
{
lean_dec_ref_known(v_a_3031_, 2);
lean_dec_ref_known(v___x_3020_, 14);
lean_dec(v_stx_2995_);
return v___x_3037_;
}
else
{
lean_object* v_id_3040_; uint8_t v___x_3041_; 
v_id_3040_ = lean_ctor_get(v_a_3031_, 0);
lean_inc(v_id_3040_);
lean_dec_ref_known(v_a_3031_, 2);
v___x_3041_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3035_, v_id_3040_);
lean_dec(v_id_3040_);
if (v___x_3041_ == 0)
{
lean_dec_ref_known(v___x_3020_, 14);
lean_dec(v_stx_2995_);
return v___x_3037_;
}
else
{
lean_object* v___x_3042_; 
lean_dec_ref(v___x_3037_);
v___x_3042_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v___x_3020_, v_a_3001_);
lean_dec_ref_known(v___x_3020_, 14);
return v___x_3042_;
}
}
}
else
{
lean_dec(v_a_3031_);
lean_dec_ref_known(v___x_3020_, 14);
lean_dec(v_stx_2995_);
return v___x_3037_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
return v_res_3055_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1));
v___x_3063_ = l_Lean_Expr_const___override(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3064_; lean_object* v_ty_x3f_3065_; 
v___x_3064_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v_ty_x3f_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3065_, 0, v___x_3064_);
return v_ty_x3f_3065_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_3067_ = l_Lean_MessageData_ofExpr(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
v___x_3069_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3072_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_ty_x3f_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v_fileName_3088_; lean_object* v_fileMap_3089_; lean_object* v_options_3090_; lean_object* v_currRecDepth_3091_; lean_object* v_maxRecDepth_3092_; lean_object* v_ref_3093_; lean_object* v_currNamespace_3094_; lean_object* v_openDecls_3095_; lean_object* v_initHeartbeats_3096_; lean_object* v_maxHeartbeats_3097_; lean_object* v_quotContext_3098_; lean_object* v_currMacroScope_3099_; uint8_t v_diag_3100_; lean_object* v_cancelTk_x3f_3101_; uint8_t v_suppressElabErrors_3102_; lean_object* v_inheritedTraceOptions_3103_; uint8_t v___x_3104_; lean_object* v_ref_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_ty_x3f_3082_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
v___x_3083_ = 1;
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_box(v___x_3083_);
v___x_3086_ = lean_box(v___x_3083_);
lean_inc(v_stx_3074_);
v___x_3087_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3087_, 0, v_stx_3074_);
lean_closure_set(v___x_3087_, 1, v_ty_x3f_3082_);
lean_closure_set(v___x_3087_, 2, v___x_3085_);
lean_closure_set(v___x_3087_, 3, v___x_3086_);
lean_closure_set(v___x_3087_, 4, v___x_3084_);
v_fileName_3088_ = lean_ctor_get(v_a_3079_, 0);
v_fileMap_3089_ = lean_ctor_get(v_a_3079_, 1);
v_options_3090_ = lean_ctor_get(v_a_3079_, 2);
v_currRecDepth_3091_ = lean_ctor_get(v_a_3079_, 3);
v_maxRecDepth_3092_ = lean_ctor_get(v_a_3079_, 4);
v_ref_3093_ = lean_ctor_get(v_a_3079_, 5);
v_currNamespace_3094_ = lean_ctor_get(v_a_3079_, 6);
v_openDecls_3095_ = lean_ctor_get(v_a_3079_, 7);
v_initHeartbeats_3096_ = lean_ctor_get(v_a_3079_, 8);
v_maxHeartbeats_3097_ = lean_ctor_get(v_a_3079_, 9);
v_quotContext_3098_ = lean_ctor_get(v_a_3079_, 10);
v_currMacroScope_3099_ = lean_ctor_get(v_a_3079_, 11);
v_diag_3100_ = lean_ctor_get_uint8(v_a_3079_, sizeof(void*)*14);
v_cancelTk_x3f_3101_ = lean_ctor_get(v_a_3079_, 12);
v_suppressElabErrors_3102_ = lean_ctor_get_uint8(v_a_3079_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3103_ = lean_ctor_get(v_a_3079_, 13);
v___x_3104_ = 1;
v_ref_3105_ = l_Lean_replaceRef(v_stx_3074_, v_ref_3093_);
lean_dec(v_stx_3074_);
lean_inc_ref(v_inheritedTraceOptions_3103_);
lean_inc(v_cancelTk_x3f_3101_);
lean_inc(v_currMacroScope_3099_);
lean_inc(v_quotContext_3098_);
lean_inc(v_maxHeartbeats_3097_);
lean_inc(v_initHeartbeats_3096_);
lean_inc(v_openDecls_3095_);
lean_inc(v_currNamespace_3094_);
lean_inc(v_maxRecDepth_3092_);
lean_inc(v_currRecDepth_3091_);
lean_inc_ref(v_options_3090_);
lean_inc_ref(v_fileMap_3089_);
lean_inc_ref(v_fileName_3088_);
v___x_3106_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3106_, 0, v_fileName_3088_);
lean_ctor_set(v___x_3106_, 1, v_fileMap_3089_);
lean_ctor_set(v___x_3106_, 2, v_options_3090_);
lean_ctor_set(v___x_3106_, 3, v_currRecDepth_3091_);
lean_ctor_set(v___x_3106_, 4, v_maxRecDepth_3092_);
lean_ctor_set(v___x_3106_, 5, v_ref_3105_);
lean_ctor_set(v___x_3106_, 6, v_currNamespace_3094_);
lean_ctor_set(v___x_3106_, 7, v_openDecls_3095_);
lean_ctor_set(v___x_3106_, 8, v_initHeartbeats_3096_);
lean_ctor_set(v___x_3106_, 9, v_maxHeartbeats_3097_);
lean_ctor_set(v___x_3106_, 10, v_quotContext_3098_);
lean_ctor_set(v___x_3106_, 11, v_currMacroScope_3099_);
lean_ctor_set(v___x_3106_, 12, v_cancelTk_x3f_3101_);
lean_ctor_set(v___x_3106_, 13, v_inheritedTraceOptions_3103_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*14, v_diag_3100_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*14 + 1, v_suppressElabErrors_3102_);
v___x_3107_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3087_, v___x_3104_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v___x_3106_, v_a_3080_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3109_; lean_object* v_a_3110_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; uint8_t v___y_3121_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; uint8_t v___x_3205_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3108_, v_a_3078_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
v___x_3205_ = l_Lean_Expr_hasSorry(v_a_3110_);
if (v___x_3205_ == 0)
{
v___y_3150_ = v_a_3075_;
v___y_3151_ = v_a_3076_;
v___y_3152_ = v_a_3077_;
v___y_3153_ = v_a_3078_;
v___y_3154_ = v___x_3106_;
v___y_3155_ = v_a_3080_;
goto v___jp_3149_;
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = l_Lean_Expr_hasSyntheticSorry(v_a_3110_);
if (v___x_3206_ == 0)
{
v___y_3187_ = v_a_3075_;
v___y_3188_ = v_a_3076_;
v___y_3189_ = v_a_3077_;
v___y_3190_ = v_a_3078_;
v___y_3191_ = v___x_3106_;
v___y_3192_ = v_a_3080_;
goto v___jp_3186_;
}
else
{
lean_object* v___x_3207_; lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_a_3110_);
lean_dec_ref_known(v___x_3106_, 14);
v___x_3207_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
v___jp_3111_:
{
if (v___y_3121_ == 0)
{
if (lean_obj_tag(v___y_3119_) == 0)
{
lean_dec_ref_known(v___y_3119_, 2);
lean_dec_ref(v___y_3118_);
lean_dec(v_a_3110_);
return v___y_3112_;
}
else
{
lean_object* v_id_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3135_; 
v_id_3122_ = lean_ctor_get(v___y_3119_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___y_3119_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v___y_3119_, 1);
lean_dec(v_unused_3136_);
v___x_3124_ = v___y_3119_;
v_isShared_3125_ = v_isSharedCheck_3135_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_id_3122_);
lean_dec(v___y_3119_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3135_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
uint8_t v___x_3126_; 
v___x_3126_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3115_, v_id_3122_);
lean_dec(v_id_3122_);
if (v___x_3126_ == 0)
{
lean_del_object(v___x_3124_);
lean_dec_ref(v___y_3118_);
lean_dec(v_a_3110_);
return v___y_3112_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_dec_ref(v___y_3112_);
v___x_3127_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
v___x_3128_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3129_ = l_Lean_indentExpr(v_a_3110_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set_tag(v___x_3124_, 7);
lean_ctor_set(v___x_3124_, 1, v___x_3129_);
lean_ctor_set(v___x_3124_, 0, v___x_3128_);
v___x_3131_ = v___x_3124_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___x_3127_);
v___x_3133_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3132_, v___y_3114_, v___y_3113_, v___y_3117_, v___y_3116_, v___y_3118_, v___y_3120_);
lean_dec_ref(v___y_3118_);
return v___x_3133_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v_a_3110_);
return v___y_3112_;
}
}
v___jp_3137_:
{
lean_object* v___x_3144_; 
lean_inc(v_a_3110_);
v___x_3144_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_3110_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_dec_ref(v___y_3142_);
lean_dec(v_a_3110_);
return v___x_3144_;
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
v___x_3146_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3147_ = l_Lean_Exception_isInterrupt(v_a_3145_);
if (v___x_3147_ == 0)
{
uint8_t v___x_3148_; 
lean_inc(v_a_3145_);
v___x_3148_ = l_Lean_Exception_isRuntime(v_a_3145_);
v___y_3112_ = v___x_3144_;
v___y_3113_ = v___y_3139_;
v___y_3114_ = v___y_3138_;
v___y_3115_ = v___x_3146_;
v___y_3116_ = v___y_3141_;
v___y_3117_ = v___y_3140_;
v___y_3118_ = v___y_3142_;
v___y_3119_ = v_a_3145_;
v___y_3120_ = v___y_3143_;
v___y_3121_ = v___x_3148_;
goto v___jp_3111_;
}
else
{
v___y_3112_ = v___x_3144_;
v___y_3113_ = v___y_3139_;
v___y_3114_ = v___y_3138_;
v___y_3115_ = v___x_3146_;
v___y_3116_ = v___y_3141_;
v___y_3117_ = v___y_3140_;
v___y_3118_ = v___y_3142_;
v___y_3119_ = v_a_3145_;
v___y_3120_ = v___y_3143_;
v___y_3121_ = v___x_3147_;
goto v___jp_3111_;
}
}
}
v___jp_3149_:
{
lean_object* v___x_3156_; 
lean_inc(v_a_3110_);
v___x_3156_ = l_Lean_Meta_getMVars(v_a_3110_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3157_, v___x_3084_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v_a_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; uint8_t v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = lean_unbox(v_a_3159_);
lean_dec(v_a_3159_);
if (v___x_3160_ == 0)
{
v___y_3138_ = v___y_3150_;
v___y_3139_ = v___y_3151_;
v___y_3140_ = v___y_3152_;
v___y_3141_ = v___y_3153_;
v___y_3142_ = v___y_3154_;
v___y_3143_ = v___y_3155_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3161_; lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v___y_3154_);
lean_dec(v_a_3110_);
v___x_3161_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v___y_3154_);
lean_dec(v_a_3110_);
v_a_3170_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3158_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3158_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v___y_3154_);
lean_dec(v_a_3110_);
v_a_3178_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3156_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3156_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
v___jp_3186_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v___x_3193_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3194_ = l_Lean_indentExpr(v_a_3110_);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3195_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec_ref(v___y_3191_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref_known(v___x_3106_, 14);
v_a_3216_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3107_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3107_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(lean_object* v_stx_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_fileName_3241_; lean_object* v_fileMap_3242_; lean_object* v_options_3243_; lean_object* v_currRecDepth_3244_; lean_object* v_maxRecDepth_3245_; lean_object* v_ref_3246_; lean_object* v_currNamespace_3247_; lean_object* v_openDecls_3248_; lean_object* v_initHeartbeats_3249_; lean_object* v_maxHeartbeats_3250_; lean_object* v_quotContext_3251_; lean_object* v_currMacroScope_3252_; uint8_t v_diag_3253_; lean_object* v_cancelTk_x3f_3254_; uint8_t v_suppressElabErrors_3255_; lean_object* v_inheritedTraceOptions_3256_; lean_object* v_ref_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_fileName_3241_ = lean_ctor_get(v_a_3238_, 0);
v_fileMap_3242_ = lean_ctor_get(v_a_3238_, 1);
v_options_3243_ = lean_ctor_get(v_a_3238_, 2);
v_currRecDepth_3244_ = lean_ctor_get(v_a_3238_, 3);
v_maxRecDepth_3245_ = lean_ctor_get(v_a_3238_, 4);
v_ref_3246_ = lean_ctor_get(v_a_3238_, 5);
v_currNamespace_3247_ = lean_ctor_get(v_a_3238_, 6);
v_openDecls_3248_ = lean_ctor_get(v_a_3238_, 7);
v_initHeartbeats_3249_ = lean_ctor_get(v_a_3238_, 8);
v_maxHeartbeats_3250_ = lean_ctor_get(v_a_3238_, 9);
v_quotContext_3251_ = lean_ctor_get(v_a_3238_, 10);
v_currMacroScope_3252_ = lean_ctor_get(v_a_3238_, 11);
v_diag_3253_ = lean_ctor_get_uint8(v_a_3238_, sizeof(void*)*14);
v_cancelTk_x3f_3254_ = lean_ctor_get(v_a_3238_, 12);
v_suppressElabErrors_3255_ = lean_ctor_get_uint8(v_a_3238_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3256_ = lean_ctor_get(v_a_3238_, 13);
v_ref_3257_ = l_Lean_replaceRef(v_stx_3233_, v_ref_3246_);
lean_inc_ref(v_inheritedTraceOptions_3256_);
lean_inc(v_cancelTk_x3f_3254_);
lean_inc(v_currMacroScope_3252_);
lean_inc(v_quotContext_3251_);
lean_inc(v_maxHeartbeats_3250_);
lean_inc(v_initHeartbeats_3249_);
lean_inc(v_openDecls_3248_);
lean_inc(v_currNamespace_3247_);
lean_inc(v_maxRecDepth_3245_);
lean_inc(v_currRecDepth_3244_);
lean_inc_ref(v_options_3243_);
lean_inc_ref(v_fileMap_3242_);
lean_inc_ref(v_fileName_3241_);
v___x_3258_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3258_, 0, v_fileName_3241_);
lean_ctor_set(v___x_3258_, 1, v_fileMap_3242_);
lean_ctor_set(v___x_3258_, 2, v_options_3243_);
lean_ctor_set(v___x_3258_, 3, v_currRecDepth_3244_);
lean_ctor_set(v___x_3258_, 4, v_maxRecDepth_3245_);
lean_ctor_set(v___x_3258_, 5, v_ref_3257_);
lean_ctor_set(v___x_3258_, 6, v_currNamespace_3247_);
lean_ctor_set(v___x_3258_, 7, v_openDecls_3248_);
lean_ctor_set(v___x_3258_, 8, v_initHeartbeats_3249_);
lean_ctor_set(v___x_3258_, 9, v_maxHeartbeats_3250_);
lean_ctor_set(v___x_3258_, 10, v_quotContext_3251_);
lean_ctor_set(v___x_3258_, 11, v_currMacroScope_3252_);
lean_ctor_set(v___x_3258_, 12, v_cancelTk_x3f_3254_);
lean_ctor_set(v___x_3258_, 13, v_inheritedTraceOptions_3256_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*14, v_diag_3253_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*14 + 1, v_suppressElabErrors_3255_);
lean_inc(v_stx_3233_);
v___x_3259_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_stx_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v___x_3258_, v_a_3239_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref_known(v___x_3258_, 14);
lean_dec(v_stx_3233_);
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_fst_3264_; lean_object* v___x_3266_; 
v_fst_3264_ = lean_ctor_get(v_a_3260_, 0);
lean_inc(v_fst_3264_);
lean_dec(v_a_3260_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v_fst_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_fst_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3284_; 
v_a_3269_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3271_ = v___x_3259_;
v_isShared_3272_ = v_isSharedCheck_3284_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3259_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3284_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3269_);
if (v_isShared_3272_ == 0)
{
v___x_3275_ = v___x_3271_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3269_);
v___x_3275_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
uint8_t v___y_3277_; uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_Exception_isInterrupt(v_a_3269_);
if (v___x_3281_ == 0)
{
uint8_t v___x_3282_; 
lean_inc(v_a_3269_);
v___x_3282_ = l_Lean_Exception_isRuntime(v_a_3269_);
v___y_3277_ = v___x_3282_;
goto v___jp_3276_;
}
else
{
v___y_3277_ = v___x_3281_;
goto v___jp_3276_;
}
v___jp_3276_:
{
if (v___y_3277_ == 0)
{
if (lean_obj_tag(v_a_3269_) == 0)
{
lean_dec_ref_known(v_a_3269_, 2);
lean_dec_ref_known(v___x_3258_, 14);
lean_dec(v_stx_3233_);
return v___x_3275_;
}
else
{
lean_object* v_id_3278_; uint8_t v___x_3279_; 
v_id_3278_ = lean_ctor_get(v_a_3269_, 0);
lean_inc(v_id_3278_);
lean_dec_ref_known(v_a_3269_, 2);
v___x_3279_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3273_, v_id_3278_);
lean_dec(v_id_3278_);
if (v___x_3279_ == 0)
{
lean_dec_ref_known(v___x_3258_, 14);
lean_dec(v_stx_3233_);
return v___x_3275_;
}
else
{
lean_object* v___x_3280_; 
lean_dec_ref(v___x_3275_);
v___x_3280_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v___x_3258_, v_a_3239_);
lean_dec_ref_known(v___x_3258_, 14);
return v___x_3280_;
}
}
}
else
{
lean_dec(v_a_3269_);
lean_dec_ref_known(v___x_3258_, 14);
lean_dec(v_stx_3233_);
return v___x_3275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
return v_res_3293_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
v___x_3295_ = l_Lean_MessageData_ofExpr(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
v___x_3297_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v___x_3296_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3300_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(lean_object* v_stx_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_ty_x3f_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v_fileName_3316_; lean_object* v_fileMap_3317_; lean_object* v_options_3318_; lean_object* v_currRecDepth_3319_; lean_object* v_maxRecDepth_3320_; lean_object* v_ref_3321_; lean_object* v_currNamespace_3322_; lean_object* v_openDecls_3323_; lean_object* v_initHeartbeats_3324_; lean_object* v_maxHeartbeats_3325_; lean_object* v_quotContext_3326_; lean_object* v_currMacroScope_3327_; uint8_t v_diag_3328_; lean_object* v_cancelTk_x3f_3329_; uint8_t v_suppressElabErrors_3330_; lean_object* v_inheritedTraceOptions_3331_; uint8_t v___x_3332_; lean_object* v_ref_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_ty_x3f_3310_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
v___x_3311_ = 1;
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_box(v___x_3311_);
v___x_3314_ = lean_box(v___x_3311_);
lean_inc(v_stx_3302_);
v___x_3315_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3315_, 0, v_stx_3302_);
lean_closure_set(v___x_3315_, 1, v_ty_x3f_3310_);
lean_closure_set(v___x_3315_, 2, v___x_3313_);
lean_closure_set(v___x_3315_, 3, v___x_3314_);
lean_closure_set(v___x_3315_, 4, v___x_3312_);
v_fileName_3316_ = lean_ctor_get(v_a_3307_, 0);
v_fileMap_3317_ = lean_ctor_get(v_a_3307_, 1);
v_options_3318_ = lean_ctor_get(v_a_3307_, 2);
v_currRecDepth_3319_ = lean_ctor_get(v_a_3307_, 3);
v_maxRecDepth_3320_ = lean_ctor_get(v_a_3307_, 4);
v_ref_3321_ = lean_ctor_get(v_a_3307_, 5);
v_currNamespace_3322_ = lean_ctor_get(v_a_3307_, 6);
v_openDecls_3323_ = lean_ctor_get(v_a_3307_, 7);
v_initHeartbeats_3324_ = lean_ctor_get(v_a_3307_, 8);
v_maxHeartbeats_3325_ = lean_ctor_get(v_a_3307_, 9);
v_quotContext_3326_ = lean_ctor_get(v_a_3307_, 10);
v_currMacroScope_3327_ = lean_ctor_get(v_a_3307_, 11);
v_diag_3328_ = lean_ctor_get_uint8(v_a_3307_, sizeof(void*)*14);
v_cancelTk_x3f_3329_ = lean_ctor_get(v_a_3307_, 12);
v_suppressElabErrors_3330_ = lean_ctor_get_uint8(v_a_3307_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3331_ = lean_ctor_get(v_a_3307_, 13);
v___x_3332_ = 1;
v_ref_3333_ = l_Lean_replaceRef(v_stx_3302_, v_ref_3321_);
lean_dec(v_stx_3302_);
lean_inc_ref(v_inheritedTraceOptions_3331_);
lean_inc(v_cancelTk_x3f_3329_);
lean_inc(v_currMacroScope_3327_);
lean_inc(v_quotContext_3326_);
lean_inc(v_maxHeartbeats_3325_);
lean_inc(v_initHeartbeats_3324_);
lean_inc(v_openDecls_3323_);
lean_inc(v_currNamespace_3322_);
lean_inc(v_maxRecDepth_3320_);
lean_inc(v_currRecDepth_3319_);
lean_inc_ref(v_options_3318_);
lean_inc_ref(v_fileMap_3317_);
lean_inc_ref(v_fileName_3316_);
v___x_3334_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3334_, 0, v_fileName_3316_);
lean_ctor_set(v___x_3334_, 1, v_fileMap_3317_);
lean_ctor_set(v___x_3334_, 2, v_options_3318_);
lean_ctor_set(v___x_3334_, 3, v_currRecDepth_3319_);
lean_ctor_set(v___x_3334_, 4, v_maxRecDepth_3320_);
lean_ctor_set(v___x_3334_, 5, v_ref_3333_);
lean_ctor_set(v___x_3334_, 6, v_currNamespace_3322_);
lean_ctor_set(v___x_3334_, 7, v_openDecls_3323_);
lean_ctor_set(v___x_3334_, 8, v_initHeartbeats_3324_);
lean_ctor_set(v___x_3334_, 9, v_maxHeartbeats_3325_);
lean_ctor_set(v___x_3334_, 10, v_quotContext_3326_);
lean_ctor_set(v___x_3334_, 11, v_currMacroScope_3327_);
lean_ctor_set(v___x_3334_, 12, v_cancelTk_x3f_3329_);
lean_ctor_set(v___x_3334_, 13, v_inheritedTraceOptions_3331_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*14, v_diag_3328_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*14 + 1, v_suppressElabErrors_3330_);
v___x_3335_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3315_, v___x_3332_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v___x_3334_, v_a_3308_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; uint8_t v___y_3349_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; uint8_t v___x_3433_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3336_, v_a_3306_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
v___x_3433_ = l_Lean_Expr_hasSorry(v_a_3338_);
if (v___x_3433_ == 0)
{
v___y_3378_ = v_a_3303_;
v___y_3379_ = v_a_3304_;
v___y_3380_ = v_a_3305_;
v___y_3381_ = v_a_3306_;
v___y_3382_ = v___x_3334_;
v___y_3383_ = v_a_3308_;
goto v___jp_3377_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = l_Lean_Expr_hasSyntheticSorry(v_a_3338_);
if (v___x_3434_ == 0)
{
v___y_3415_ = v_a_3303_;
v___y_3416_ = v_a_3304_;
v___y_3417_ = v_a_3305_;
v___y_3418_ = v_a_3306_;
v___y_3419_ = v___x_3334_;
v___y_3420_ = v_a_3308_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3435_; lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_a_3338_);
lean_dec_ref_known(v___x_3334_, 14);
v___x_3435_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
v___jp_3339_:
{
if (v___y_3349_ == 0)
{
if (lean_obj_tag(v___y_3343_) == 0)
{
lean_dec_ref_known(v___y_3343_, 2);
lean_dec_ref(v___y_3348_);
lean_dec(v_a_3338_);
return v___y_3342_;
}
else
{
lean_object* v_id_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3363_; 
v_id_3350_ = lean_ctor_get(v___y_3343_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___y_3343_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v___y_3343_, 1);
lean_dec(v_unused_3364_);
v___x_3352_ = v___y_3343_;
v_isShared_3353_ = v_isSharedCheck_3363_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_id_3350_);
lean_dec(v___y_3343_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3363_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
uint8_t v___x_3354_; 
v___x_3354_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3341_, v_id_3350_);
lean_dec(v_id_3350_);
if (v___x_3354_ == 0)
{
lean_del_object(v___x_3352_);
lean_dec_ref(v___y_3348_);
lean_dec(v_a_3338_);
return v___y_3342_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; 
lean_dec_ref(v___y_3342_);
v___x_3355_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
v___x_3356_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3357_ = l_Lean_indentExpr(v_a_3338_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 7);
lean_ctor_set(v___x_3352_, 1, v___x_3357_);
lean_ctor_set(v___x_3352_, 0, v___x_3356_);
v___x_3359_ = v___x_3352_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
lean_ctor_set(v___x_3360_, 1, v___x_3355_);
v___x_3361_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3360_, v___y_3346_, v___y_3347_, v___y_3344_, v___y_3345_, v___y_3348_, v___y_3340_);
lean_dec_ref(v___y_3348_);
return v___x_3361_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3348_);
lean_dec_ref(v___y_3343_);
lean_dec(v_a_3338_);
return v___y_3342_;
}
}
v___jp_3365_:
{
lean_object* v___x_3372_; 
lean_inc(v_a_3338_);
v___x_3372_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_3338_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_dec_ref(v___y_3370_);
lean_dec(v_a_3338_);
return v___x_3372_;
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
v___x_3374_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3375_ = l_Lean_Exception_isInterrupt(v_a_3373_);
if (v___x_3375_ == 0)
{
uint8_t v___x_3376_; 
lean_inc(v_a_3373_);
v___x_3376_ = l_Lean_Exception_isRuntime(v_a_3373_);
v___y_3340_ = v___y_3371_;
v___y_3341_ = v___x_3374_;
v___y_3342_ = v___x_3372_;
v___y_3343_ = v_a_3373_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3366_;
v___y_3347_ = v___y_3367_;
v___y_3348_ = v___y_3370_;
v___y_3349_ = v___x_3376_;
goto v___jp_3339_;
}
else
{
v___y_3340_ = v___y_3371_;
v___y_3341_ = v___x_3374_;
v___y_3342_ = v___x_3372_;
v___y_3343_ = v_a_3373_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3366_;
v___y_3347_ = v___y_3367_;
v___y_3348_ = v___y_3370_;
v___y_3349_ = v___x_3375_;
goto v___jp_3339_;
}
}
}
v___jp_3377_:
{
lean_object* v___x_3384_; 
lean_inc(v_a_3338_);
v___x_3384_ = l_Lean_Meta_getMVars(v_a_3338_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3385_, v___x_3312_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v_a_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; uint8_t v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = lean_unbox(v_a_3387_);
lean_dec(v_a_3387_);
if (v___x_3388_ == 0)
{
v___y_3366_ = v___y_3378_;
v___y_3367_ = v___y_3379_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3381_;
v___y_3370_ = v___y_3382_;
v___y_3371_ = v___y_3383_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3389_; lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref(v___y_3382_);
lean_dec(v_a_3338_);
v___x_3389_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v___y_3382_);
lean_dec(v_a_3338_);
v_a_3398_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3386_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3386_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v___y_3382_);
lean_dec(v_a_3338_);
v_a_3406_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3384_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3384_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
v___jp_3414_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v___x_3421_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3422_ = l_Lean_indentExpr(v_a_3338_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3423_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec_ref(v___y_3419_);
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
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref_known(v___x_3334_, 14);
v_a_3444_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3335_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3335_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(lean_object* v_stx_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
return v_res_3460_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = lean_box(0);
v___x_3467_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_3468_ = l_Lean_Expr_const___override(v___x_3467_, v___x_3466_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3469_; lean_object* v_ty_x3f_3470_; 
v___x_3469_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_3470_, 0, v___x_3469_);
return v_ty_x3f_3470_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_3472_ = l_Lean_MessageData_ofExpr(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_3474_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3, &l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
v___x_3477_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v___x_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v_ty_x3f_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v_fileName_3493_; lean_object* v_fileMap_3494_; lean_object* v_options_3495_; lean_object* v_currRecDepth_3496_; lean_object* v_maxRecDepth_3497_; lean_object* v_ref_3498_; lean_object* v_currNamespace_3499_; lean_object* v_openDecls_3500_; lean_object* v_initHeartbeats_3501_; lean_object* v_maxHeartbeats_3502_; lean_object* v_quotContext_3503_; lean_object* v_currMacroScope_3504_; uint8_t v_diag_3505_; lean_object* v_cancelTk_x3f_3506_; uint8_t v_suppressElabErrors_3507_; lean_object* v_inheritedTraceOptions_3508_; uint8_t v___x_3509_; lean_object* v_ref_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v_ty_x3f_3487_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_3488_ = 1;
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_box(v___x_3488_);
v___x_3491_ = lean_box(v___x_3488_);
lean_inc(v_stx_3479_);
v___x_3492_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3492_, 0, v_stx_3479_);
lean_closure_set(v___x_3492_, 1, v_ty_x3f_3487_);
lean_closure_set(v___x_3492_, 2, v___x_3490_);
lean_closure_set(v___x_3492_, 3, v___x_3491_);
lean_closure_set(v___x_3492_, 4, v___x_3489_);
v_fileName_3493_ = lean_ctor_get(v_a_3484_, 0);
v_fileMap_3494_ = lean_ctor_get(v_a_3484_, 1);
v_options_3495_ = lean_ctor_get(v_a_3484_, 2);
v_currRecDepth_3496_ = lean_ctor_get(v_a_3484_, 3);
v_maxRecDepth_3497_ = lean_ctor_get(v_a_3484_, 4);
v_ref_3498_ = lean_ctor_get(v_a_3484_, 5);
v_currNamespace_3499_ = lean_ctor_get(v_a_3484_, 6);
v_openDecls_3500_ = lean_ctor_get(v_a_3484_, 7);
v_initHeartbeats_3501_ = lean_ctor_get(v_a_3484_, 8);
v_maxHeartbeats_3502_ = lean_ctor_get(v_a_3484_, 9);
v_quotContext_3503_ = lean_ctor_get(v_a_3484_, 10);
v_currMacroScope_3504_ = lean_ctor_get(v_a_3484_, 11);
v_diag_3505_ = lean_ctor_get_uint8(v_a_3484_, sizeof(void*)*14);
v_cancelTk_x3f_3506_ = lean_ctor_get(v_a_3484_, 12);
v_suppressElabErrors_3507_ = lean_ctor_get_uint8(v_a_3484_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3508_ = lean_ctor_get(v_a_3484_, 13);
v___x_3509_ = 1;
v_ref_3510_ = l_Lean_replaceRef(v_stx_3479_, v_ref_3498_);
lean_dec(v_stx_3479_);
lean_inc_ref(v_inheritedTraceOptions_3508_);
lean_inc(v_cancelTk_x3f_3506_);
lean_inc(v_currMacroScope_3504_);
lean_inc(v_quotContext_3503_);
lean_inc(v_maxHeartbeats_3502_);
lean_inc(v_initHeartbeats_3501_);
lean_inc(v_openDecls_3500_);
lean_inc(v_currNamespace_3499_);
lean_inc(v_maxRecDepth_3497_);
lean_inc(v_currRecDepth_3496_);
lean_inc_ref(v_options_3495_);
lean_inc_ref(v_fileMap_3494_);
lean_inc_ref(v_fileName_3493_);
v___x_3511_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3511_, 0, v_fileName_3493_);
lean_ctor_set(v___x_3511_, 1, v_fileMap_3494_);
lean_ctor_set(v___x_3511_, 2, v_options_3495_);
lean_ctor_set(v___x_3511_, 3, v_currRecDepth_3496_);
lean_ctor_set(v___x_3511_, 4, v_maxRecDepth_3497_);
lean_ctor_set(v___x_3511_, 5, v_ref_3510_);
lean_ctor_set(v___x_3511_, 6, v_currNamespace_3499_);
lean_ctor_set(v___x_3511_, 7, v_openDecls_3500_);
lean_ctor_set(v___x_3511_, 8, v_initHeartbeats_3501_);
lean_ctor_set(v___x_3511_, 9, v_maxHeartbeats_3502_);
lean_ctor_set(v___x_3511_, 10, v_quotContext_3503_);
lean_ctor_set(v___x_3511_, 11, v_currMacroScope_3504_);
lean_ctor_set(v___x_3511_, 12, v_cancelTk_x3f_3506_);
lean_ctor_set(v___x_3511_, 13, v_inheritedTraceOptions_3508_);
lean_ctor_set_uint8(v___x_3511_, sizeof(void*)*14, v_diag_3505_);
lean_ctor_set_uint8(v___x_3511_, sizeof(void*)*14 + 1, v_suppressElabErrors_3507_);
v___x_3512_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3492_, v___x_3509_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v___x_3511_, v_a_3485_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3514_; lean_object* v_a_3515_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___x_3610_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___x_3514_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_3513_, v_a_3483_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref(v___x_3514_);
v___x_3610_ = l_Lean_Expr_hasSorry(v_a_3515_);
if (v___x_3610_ == 0)
{
v___y_3555_ = v_a_3480_;
v___y_3556_ = v_a_3481_;
v___y_3557_ = v_a_3482_;
v___y_3558_ = v_a_3483_;
v___y_3559_ = v___x_3511_;
v___y_3560_ = v_a_3485_;
goto v___jp_3554_;
}
else
{
uint8_t v___x_3611_; 
v___x_3611_ = l_Lean_Expr_hasSyntheticSorry(v_a_3515_);
if (v___x_3611_ == 0)
{
v___y_3592_ = v_a_3480_;
v___y_3593_ = v_a_3481_;
v___y_3594_ = v_a_3482_;
v___y_3595_ = v_a_3483_;
v___y_3596_ = v___x_3511_;
v___y_3597_ = v_a_3485_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3612_; lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v_a_3515_);
lean_dec_ref_known(v___x_3511_, 14);
v___x_3612_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
v___jp_3516_:
{
if (v___y_3526_ == 0)
{
if (lean_obj_tag(v___y_3522_) == 0)
{
lean_dec_ref_known(v___y_3522_, 2);
lean_dec_ref(v___y_3520_);
lean_dec(v_a_3515_);
return v___y_3517_;
}
else
{
lean_object* v_id_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3540_; 
v_id_3527_ = lean_ctor_get(v___y_3522_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___y_3522_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; 
v_unused_3541_ = lean_ctor_get(v___y_3522_, 1);
lean_dec(v_unused_3541_);
v___x_3529_ = v___y_3522_;
v_isShared_3530_ = v_isSharedCheck_3540_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_id_3527_);
lean_dec(v___y_3522_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3540_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
uint8_t v___x_3531_; 
v___x_3531_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3524_, v_id_3527_);
lean_dec(v_id_3527_);
if (v___x_3531_ == 0)
{
lean_del_object(v___x_3529_);
lean_dec_ref(v___y_3520_);
lean_dec(v_a_3515_);
return v___y_3517_;
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
lean_dec_ref(v___y_3517_);
v___x_3532_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_3533_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
v___x_3534_ = l_Lean_indentExpr(v_a_3515_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set_tag(v___x_3529_, 7);
lean_ctor_set(v___x_3529_, 1, v___x_3534_);
lean_ctor_set(v___x_3529_, 0, v___x_3533_);
v___x_3536_ = v___x_3529_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v___x_3532_);
v___x_3538_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3537_, v___y_3525_, v___y_3523_, v___y_3519_, v___y_3518_, v___y_3520_, v___y_3521_);
lean_dec_ref(v___y_3520_);
return v___x_3538_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3520_);
lean_dec(v_a_3515_);
return v___y_3517_;
}
}
v___jp_3542_:
{
lean_object* v___x_3549_; 
lean_inc(v_a_3515_);
v___x_3549_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_3515_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref(v___y_3547_);
lean_dec(v_a_3515_);
return v___x_3549_;
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
v___x_3551_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3552_ = l_Lean_Exception_isInterrupt(v_a_3550_);
if (v___x_3552_ == 0)
{
uint8_t v___x_3553_; 
lean_inc(v_a_3550_);
v___x_3553_ = l_Lean_Exception_isRuntime(v_a_3550_);
v___y_3517_ = v___x_3549_;
v___y_3518_ = v___y_3546_;
v___y_3519_ = v___y_3545_;
v___y_3520_ = v___y_3547_;
v___y_3521_ = v___y_3548_;
v___y_3522_ = v_a_3550_;
v___y_3523_ = v___y_3544_;
v___y_3524_ = v___x_3551_;
v___y_3525_ = v___y_3543_;
v___y_3526_ = v___x_3553_;
goto v___jp_3516_;
}
else
{
v___y_3517_ = v___x_3549_;
v___y_3518_ = v___y_3546_;
v___y_3519_ = v___y_3545_;
v___y_3520_ = v___y_3547_;
v___y_3521_ = v___y_3548_;
v___y_3522_ = v_a_3550_;
v___y_3523_ = v___y_3544_;
v___y_3524_ = v___x_3551_;
v___y_3525_ = v___y_3543_;
v___y_3526_ = v___x_3552_;
goto v___jp_3516_;
}
}
}
v___jp_3554_:
{
lean_object* v___x_3561_; 
lean_inc(v_a_3515_);
v___x_3561_ = l_Lean_Meta_getMVars(v_a_3515_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3562_, v___x_3489_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v_a_3562_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; uint8_t v___x_3565_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = lean_unbox(v_a_3564_);
lean_dec(v_a_3564_);
if (v___x_3565_ == 0)
{
v___y_3543_ = v___y_3555_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3557_;
v___y_3546_ = v___y_3558_;
v___y_3547_ = v___y_3559_;
v___y_3548_ = v___y_3560_;
goto v___jp_3542_;
}
else
{
lean_object* v___x_3566_; lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref(v___y_3559_);
lean_dec(v_a_3515_);
v___x_3566_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
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
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v___y_3559_);
lean_dec(v_a_3515_);
v_a_3575_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3563_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3563_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v___y_3559_);
lean_dec(v_a_3515_);
v_a_3583_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3561_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3561_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
v___jp_3591_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
v___x_3598_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
v___x_3599_ = l_Lean_indentExpr(v_a_3515_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_3600_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec_ref(v___y_3596_);
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec_ref_known(v___x_3511_, 14);
v_a_3621_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3512_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3512_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(lean_object* v_stx_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_fileName_3646_; lean_object* v_fileMap_3647_; lean_object* v_options_3648_; lean_object* v_currRecDepth_3649_; lean_object* v_maxRecDepth_3650_; lean_object* v_ref_3651_; lean_object* v_currNamespace_3652_; lean_object* v_openDecls_3653_; lean_object* v_initHeartbeats_3654_; lean_object* v_maxHeartbeats_3655_; lean_object* v_quotContext_3656_; lean_object* v_currMacroScope_3657_; uint8_t v_diag_3658_; lean_object* v_cancelTk_x3f_3659_; uint8_t v_suppressElabErrors_3660_; lean_object* v_inheritedTraceOptions_3661_; lean_object* v_ref_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_fileName_3646_ = lean_ctor_get(v_a_3643_, 0);
v_fileMap_3647_ = lean_ctor_get(v_a_3643_, 1);
v_options_3648_ = lean_ctor_get(v_a_3643_, 2);
v_currRecDepth_3649_ = lean_ctor_get(v_a_3643_, 3);
v_maxRecDepth_3650_ = lean_ctor_get(v_a_3643_, 4);
v_ref_3651_ = lean_ctor_get(v_a_3643_, 5);
v_currNamespace_3652_ = lean_ctor_get(v_a_3643_, 6);
v_openDecls_3653_ = lean_ctor_get(v_a_3643_, 7);
v_initHeartbeats_3654_ = lean_ctor_get(v_a_3643_, 8);
v_maxHeartbeats_3655_ = lean_ctor_get(v_a_3643_, 9);
v_quotContext_3656_ = lean_ctor_get(v_a_3643_, 10);
v_currMacroScope_3657_ = lean_ctor_get(v_a_3643_, 11);
v_diag_3658_ = lean_ctor_get_uint8(v_a_3643_, sizeof(void*)*14);
v_cancelTk_x3f_3659_ = lean_ctor_get(v_a_3643_, 12);
v_suppressElabErrors_3660_ = lean_ctor_get_uint8(v_a_3643_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3661_ = lean_ctor_get(v_a_3643_, 13);
v_ref_3662_ = l_Lean_replaceRef(v_stx_3638_, v_ref_3651_);
lean_inc_ref(v_inheritedTraceOptions_3661_);
lean_inc(v_cancelTk_x3f_3659_);
lean_inc(v_currMacroScope_3657_);
lean_inc(v_quotContext_3656_);
lean_inc(v_maxHeartbeats_3655_);
lean_inc(v_initHeartbeats_3654_);
lean_inc(v_openDecls_3653_);
lean_inc(v_currNamespace_3652_);
lean_inc(v_maxRecDepth_3650_);
lean_inc(v_currRecDepth_3649_);
lean_inc_ref(v_options_3648_);
lean_inc_ref(v_fileMap_3647_);
lean_inc_ref(v_fileName_3646_);
v___x_3663_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3663_, 0, v_fileName_3646_);
lean_ctor_set(v___x_3663_, 1, v_fileMap_3647_);
lean_ctor_set(v___x_3663_, 2, v_options_3648_);
lean_ctor_set(v___x_3663_, 3, v_currRecDepth_3649_);
lean_ctor_set(v___x_3663_, 4, v_maxRecDepth_3650_);
lean_ctor_set(v___x_3663_, 5, v_ref_3662_);
lean_ctor_set(v___x_3663_, 6, v_currNamespace_3652_);
lean_ctor_set(v___x_3663_, 7, v_openDecls_3653_);
lean_ctor_set(v___x_3663_, 8, v_initHeartbeats_3654_);
lean_ctor_set(v___x_3663_, 9, v_maxHeartbeats_3655_);
lean_ctor_set(v___x_3663_, 10, v_quotContext_3656_);
lean_ctor_set(v___x_3663_, 11, v_currMacroScope_3657_);
lean_ctor_set(v___x_3663_, 12, v_cancelTk_x3f_3659_);
lean_ctor_set(v___x_3663_, 13, v_inheritedTraceOptions_3661_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*14, v_diag_3658_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*14 + 1, v_suppressElabErrors_3660_);
lean_inc(v_stx_3638_);
v___x_3664_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_stx_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v___x_3663_, v_a_3644_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3673_; 
lean_dec_ref_known(v___x_3663_, 14);
lean_dec(v_stx_3638_);
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3673_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3673_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_fst_3669_; lean_object* v___x_3671_; 
v_fst_3669_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_fst_3669_);
lean_dec(v_a_3665_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v_fst_3669_);
v___x_3671_ = v___x_3667_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_fst_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3689_; 
v_a_3674_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3676_ = v___x_3664_;
v_isShared_3677_ = v_isSharedCheck_3689_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3664_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3689_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3678_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3674_);
if (v_isShared_3677_ == 0)
{
v___x_3680_ = v___x_3676_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3674_);
v___x_3680_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
uint8_t v___y_3682_; uint8_t v___x_3686_; 
v___x_3686_ = l_Lean_Exception_isInterrupt(v_a_3674_);
if (v___x_3686_ == 0)
{
uint8_t v___x_3687_; 
lean_inc(v_a_3674_);
v___x_3687_ = l_Lean_Exception_isRuntime(v_a_3674_);
v___y_3682_ = v___x_3687_;
goto v___jp_3681_;
}
else
{
v___y_3682_ = v___x_3686_;
goto v___jp_3681_;
}
v___jp_3681_:
{
if (v___y_3682_ == 0)
{
if (lean_obj_tag(v_a_3674_) == 0)
{
lean_dec_ref_known(v_a_3674_, 2);
lean_dec_ref_known(v___x_3663_, 14);
lean_dec(v_stx_3638_);
return v___x_3680_;
}
else
{
lean_object* v_id_3683_; uint8_t v___x_3684_; 
v_id_3683_ = lean_ctor_get(v_a_3674_, 0);
lean_inc(v_id_3683_);
lean_dec_ref_known(v_a_3674_, 2);
v___x_3684_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3678_, v_id_3683_);
lean_dec(v_id_3683_);
if (v___x_3684_ == 0)
{
lean_dec_ref_known(v___x_3663_, 14);
lean_dec(v_stx_3638_);
return v___x_3680_;
}
else
{
lean_object* v___x_3685_; 
lean_dec_ref(v___x_3680_);
v___x_3685_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v___x_3663_, v_a_3644_);
lean_dec_ref_known(v___x_3663_, 14);
return v___x_3685_;
}
}
}
else
{
lean_dec(v_a_3674_);
lean_dec_ref_known(v___x_3663_, 14);
lean_dec(v_stx_3638_);
return v___x_3680_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(lean_object* v_config_3730_, lean_object* v_item_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v_item_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_3750_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3731_, v___x_3749_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3750_) == 0)
{
uint8_t v___x_3751_; 
lean_dec_ref_known(v___x_3750_, 1);
v___x_3751_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3731_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3752_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3731_);
lean_inc_ref(v_item_3731_);
v___x_3753_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3731_);
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1));
v___x_3755_ = lean_string_dec_eq(v___x_3752_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2));
v___x_3757_ = lean_string_dec_eq(v___x_3752_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3));
v___x_3759_ = lean_string_dec_eq(v___x_3752_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4));
v___x_3761_ = lean_string_dec_eq(v___x_3752_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5));
v___x_3763_ = lean_string_dec_eq(v___x_3752_, v___x_3762_);
lean_dec_ref(v___x_3752_);
if (v___x_3763_ == 0)
{
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_item_3740_ = v___x_3753_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6));
v___x_3765_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3731_, v___x_3764_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3765_) == 0)
{
uint8_t v___x_3766_; 
lean_dec_ref_known(v___x_3765_, 1);
v___x_3766_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3753_);
if (v___x_3766_ == 0)
{
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_item_3740_ = v___x_3753_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3767_; 
lean_dec_ref(v___x_3753_);
lean_inc_ref(v_item_3731_);
v___x_3767_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_value_3768_; lean_object* v___x_3769_; 
lean_dec_ref_known(v___x_3767_, 1);
v_value_3768_ = lean_ctor_get(v_item_3731_, 2);
lean_inc(v_value_3768_);
lean_dec_ref(v_item_3731_);
v___x_3769_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_3768_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3788_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3788_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3788_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
uint8_t v_offsetCnstrs_3774_; lean_object* v_occs_3775_; uint8_t v_newGoals_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3787_; 
v_offsetCnstrs_3774_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1 + 1);
v_occs_3775_ = lean_ctor_get(v_config_3730_, 0);
v_newGoals_3776_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1 + 2);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_config_3730_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3778_ = v_config_3730_;
v_isShared_3779_ = v_isSharedCheck_3787_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_occs_3775_);
lean_dec(v_config_3730_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3787_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_occs_3775_);
v___x_3781_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
uint8_t v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unbox(v_a_3770_);
lean_dec(v_a_3770_);
lean_ctor_set_uint8(v___x_3781_, sizeof(void*)*1, v___x_3782_);
lean_ctor_set_uint8(v___x_3781_, sizeof(void*)*1 + 1, v_offsetCnstrs_3774_);
lean_ctor_set_uint8(v___x_3781_, sizeof(void*)*1 + 2, v_newGoals_3776_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3781_);
v___x_3784_ = v___x_3772_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3781_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref(v_config_3730_);
v_a_3789_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3769_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3769_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3797_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3767_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3767_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3805_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3765_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3765_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
lean_dec_ref(v___x_3752_);
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7));
v___x_3814_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3731_, v___x_3813_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3814_) == 0)
{
uint8_t v___x_3815_; 
lean_dec_ref_known(v___x_3814_, 1);
v___x_3815_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3753_);
if (v___x_3815_ == 0)
{
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_item_3740_ = v___x_3753_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3816_; 
lean_dec_ref(v___x_3753_);
v___x_3816_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3835_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3835_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3835_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
uint8_t v_transparency_3821_; lean_object* v_occs_3822_; uint8_t v_newGoals_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3834_; 
v_transparency_3821_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1);
v_occs_3822_ = lean_ctor_get(v_config_3730_, 0);
v_newGoals_3823_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1 + 2);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_config_3730_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3825_ = v_config_3730_;
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_occs_3822_);
lean_dec(v_config_3730_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_occs_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3833_, sizeof(void*)*1, v_transparency_3821_);
v___x_3828_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
uint8_t v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = lean_unbox(v_a_3817_);
lean_dec(v_a_3817_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*1 + 1, v___x_3829_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*1 + 2, v_newGoals_3823_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3828_);
v___x_3831_ = v___x_3819_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3828_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v_config_3730_);
v_a_3836_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3816_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3816_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3844_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3814_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3814_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_dec_ref(v___x_3752_);
v___x_3852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8));
v___x_3853_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3731_, v___x_3852_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3853_) == 0)
{
uint8_t v___x_3854_; 
lean_dec_ref_known(v___x_3853_, 1);
v___x_3854_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3753_);
if (v___x_3854_ == 0)
{
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_item_3740_ = v___x_3753_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3855_; 
lean_dec_ref(v___x_3753_);
lean_inc_ref(v_item_3731_);
v___x_3855_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_value_3856_; lean_object* v___x_3857_; 
lean_dec_ref_known(v___x_3855_, 1);
v_value_3856_ = lean_ctor_get(v_item_3731_, 2);
lean_inc(v_value_3856_);
lean_dec_ref(v_item_3731_);
v___x_3857_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_3856_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3876_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3876_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3876_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
uint8_t v_transparency_3862_; uint8_t v_offsetCnstrs_3863_; uint8_t v_newGoals_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3874_; 
v_transparency_3862_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1);
v_offsetCnstrs_3863_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1 + 1);
v_newGoals_3864_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1 + 2);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_config_3730_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; 
v_unused_3875_ = lean_ctor_get(v_config_3730_, 0);
lean_dec(v_unused_3875_);
v___x_3866_ = v_config_3730_;
v_isShared_3867_ = v_isSharedCheck_3874_;
goto v_resetjp_3865_;
}
else
{
lean_dec(v_config_3730_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3874_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v_a_3858_);
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3858_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*1, v_transparency_3862_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*1 + 1, v_offsetCnstrs_3863_);
lean_ctor_set_uint8(v_reuseFailAlloc_3873_, sizeof(void*)*1 + 2, v_newGoals_3864_);
v___x_3869_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3871_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3869_);
v___x_3871_ = v___x_3860_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v_config_3730_);
v_a_3877_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3857_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3857_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3885_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3855_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3855_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3893_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3853_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3853_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_dec_ref(v___x_3752_);
v___x_3901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9));
v___x_3902_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3731_, v___x_3901_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3902_) == 0)
{
uint8_t v___x_3903_; 
lean_dec_ref_known(v___x_3902_, 1);
v___x_3903_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3753_);
if (v___x_3903_ == 0)
{
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_item_3740_ = v___x_3753_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3904_; 
lean_dec_ref(v___x_3753_);
lean_inc_ref(v_item_3731_);
v___x_3904_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_value_3905_; lean_object* v___x_3906_; 
lean_dec_ref_known(v___x_3904_, 1);
v_value_3905_ = lean_ctor_get(v_item_3731_, 2);
lean_inc(v_value_3905_);
lean_dec_ref(v_item_3731_);
v___x_3906_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_3905_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3925_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3925_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3925_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
uint8_t v_transparency_3911_; uint8_t v_offsetCnstrs_3912_; lean_object* v_occs_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3924_; 
v_transparency_3911_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1);
v_offsetCnstrs_3912_ = lean_ctor_get_uint8(v_config_3730_, sizeof(void*)*1 + 1);
v_occs_3913_ = lean_ctor_get(v_config_3730_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_config_3730_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3915_ = v_config_3730_;
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_occs_3913_);
lean_dec(v_config_3730_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_occs_3913_);
lean_ctor_set_uint8(v_reuseFailAlloc_3923_, sizeof(void*)*1, v_transparency_3911_);
lean_ctor_set_uint8(v_reuseFailAlloc_3923_, sizeof(void*)*1 + 1, v_offsetCnstrs_3912_);
v___x_3918_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
uint8_t v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = lean_unbox(v_a_3907_);
lean_dec(v_a_3907_);
lean_ctor_set_uint8(v___x_3918_, sizeof(void*)*1 + 2, v___x_3919_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3918_);
v___x_3921_ = v___x_3909_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3918_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec_ref(v_config_3730_);
v_a_3926_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3906_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3906_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3934_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3904_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3904_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3942_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3902_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3902_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
else
{
uint8_t v___x_3950_; 
lean_dec_ref(v___x_3752_);
lean_dec_ref(v_config_3730_);
v___x_3950_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3753_);
if (v___x_3950_ == 0)
{
lean_dec_ref(v_item_3731_);
v_item_3740_ = v___x_3753_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
else
{
lean_object* v_value_3951_; lean_object* v___x_3952_; 
lean_dec_ref(v___x_3753_);
v_value_3951_ = lean_ctor_get(v_item_3731_, 2);
lean_inc(v_value_3951_);
lean_dec_ref(v_item_3731_);
v___x_3952_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_3951_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3952_;
}
}
}
else
{
lean_dec_ref(v_config_3730_);
v_item_3740_ = v_item_3731_;
v___y_3741_ = v___y_3732_;
v___y_3742_ = v___y_3733_;
v___y_3743_ = v___y_3734_;
v___y_3744_ = v___y_3735_;
v___y_3745_ = v___y_3736_;
v___y_3746_ = v___y_3737_;
goto v___jp_3739_;
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec_ref(v_item_3731_);
lean_dec_ref(v_config_3730_);
v_a_3953_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3750_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3750_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
v___jp_3739_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0));
v___x_3748_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3740_, v___x_3747_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3961_, lean_object* v_item_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_3961_, v_item_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(lean_object* v_e_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_3973_, v___y_3977_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(lean_object* v_e_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(lean_object* v_00_u03b1_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(lean_object* v_00_u03b1_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(lean_object* v_00_u03b1_4009_, lean_object* v_msg_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(lean_object* v_00_u03b1_4019_, lean_object* v_msg_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_4019_, v_msg_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(lean_object* v_msgData_4029_, lean_object* v_macroStack_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_4029_, v_macroStack_4030_, v___y_4035_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(lean_object* v_msgData_4039_, lean_object* v_macroStack_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_4039_, v_macroStack_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
return v_res_4048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = lean_box(0);
v___x_4050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4));
v___x_4051_ = l_Lean_mkConst(v___x_4050_, v___x_4049_);
return v___x_4051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0);
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(lean_object* v_cfg_4054_, lean_object* v_cfgItem_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_obj_once(&l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1);
v___x_4064_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_4054_, v_cfgItem_4055_, v___x_4063_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(lean_object* v_cfg_4065_, lean_object* v_cfgItem_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(v_cfg_4065_, v_cfgItem_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v_cfgItem_4066_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* v_cfg_4076_, lean_object* v_init_4077_, uint8_t v_logExceptions_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v_onErr_4083_; lean_object* v_eval_4084_; 
v_onErr_4083_ = ((lean_object*)(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0));
v_eval_4084_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0));
if (v_logExceptions_4078_ == 0)
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4084_, v_init_4077_, v_cfg_4076_, v_onErr_4083_, v_logExceptions_4078_, v_a_4080_, v_a_4081_);
return v___x_4085_;
}
else
{
uint8_t v_recover_4086_; lean_object* v___x_4087_; 
v_recover_4086_ = lean_ctor_get_uint8(v_a_4079_, sizeof(void*)*1);
v___x_4087_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4084_, v_init_4077_, v_cfg_4076_, v_onErr_4083_, v_recover_4086_, v_a_4080_, v_a_4081_);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* v_cfg_4088_, lean_object* v_init_4089_, lean_object* v_logExceptions_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
uint8_t v_logExceptions_boxed_4095_; lean_object* v_res_4096_; 
v_logExceptions_boxed_4095_ = lean_unbox(v_logExceptions_4090_);
v_res_4096_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4088_, v_init_4089_, v_logExceptions_boxed_4095_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec_ref(v_a_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* v_cfg_4097_, lean_object* v_init_4098_, uint8_t v_logExceptions_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v_cfg_4097_, v_init_4098_, v_logExceptions_4099_, v_a_4100_, v_a_4106_, v_a_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* v_cfg_4110_, lean_object* v_init_4111_, lean_object* v_logExceptions_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
uint8_t v_logExceptions_boxed_4122_; lean_object* v_res_4123_; 
v_logExceptions_boxed_4122_ = lean_unbox(v_logExceptions_4112_);
v_res_4123_ = l_Lean_Elab_Tactic_elabRewriteConfig(v_cfg_4110_, v_init_4111_, v_logExceptions_boxed_4122_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_a_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_a_4116_);
lean_dec_ref(v_a_4115_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
return v_res_4123_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3));
v___x_4131_ = l_Lean_MessageData_ofFormat(v___x_4130_);
return v___x_4131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4);
v___x_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* v_x_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1));
v___x_4145_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5, &l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5);
v___x_4146_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4144_, v_x_4134_, v___x_4145_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* v_x_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(v_x_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* v_term_4158_, uint8_t v_symm_4159_, lean_object* v_a_4160_, lean_object* v_x_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Elab_Tactic_rewriteLocalDecl(v_term_4158_, v_symm_4159_, v_x_4161_, v_a_4160_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* v_term_4172_, lean_object* v_symm_4173_, lean_object* v_a_4174_, lean_object* v_x_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v_symm_boxed_4185_; lean_object* v_res_4186_; 
v_symm_boxed_4185_ = lean_unbox(v_symm_4173_);
v_res_4186_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(v_term_4172_, v_symm_boxed_4185_, v_a_4174_, v_x_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* v_a_4187_, lean_object* v___x_4188_, lean_object* v___f_4189_, uint8_t v_symm_4190_, lean_object* v_term_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4201_ = lean_box(v_symm_4190_);
lean_inc_ref(v_a_4187_);
lean_inc(v_term_4191_);
v___f_4202_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4202_, 0, v_term_4191_);
lean_closure_set(v___f_4202_, 1, v___x_4201_);
lean_closure_set(v___f_4202_, 2, v_a_4187_);
v___x_4203_ = lean_box(v_symm_4190_);
v___x_4204_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(v___x_4204_, 0, v_term_4191_);
lean_closure_set(v___x_4204_, 1, v___x_4203_);
lean_closure_set(v___x_4204_, 2, v_a_4187_);
v___x_4205_ = l_Lean_Elab_Tactic_withLocation(v___x_4188_, v___f_4202_, v___x_4204_, v___f_4189_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* v_a_4206_, lean_object* v___x_4207_, lean_object* v___f_4208_, lean_object* v_symm_4209_, lean_object* v_term_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
uint8_t v_symm_boxed_4220_; lean_object* v_res_4221_; 
v_symm_boxed_4220_ = lean_unbox(v_symm_4209_);
v_res_4221_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(v_a_4206_, v___x_4207_, v___f_4208_, v_symm_boxed_4220_, v_term_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___x_4207_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* v_stx_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4238_ = lean_unsigned_to_nat(1u);
v___x_4239_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4238_);
v___x_4240_ = 1;
v___x_4241_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0));
v___x_4242_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(v___x_4239_, v___x_4241_, v___x_4240_, v_a_4229_, v_a_4235_, v_a_4236_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___f_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___f_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
v___f_4244_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1));
v___x_4245_ = lean_unsigned_to_nat(3u);
v___x_4246_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4245_);
v___x_4247_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_4246_);
lean_dec(v___x_4246_);
v___f_4248_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(v___f_4248_, 0, v_a_4243_);
lean_closure_set(v___f_4248_, 1, v___x_4247_);
lean_closure_set(v___f_4248_, 2, v___f_4244_);
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4249_);
v___x_4251_ = lean_unsigned_to_nat(2u);
v___x_4252_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4251_);
v___x_4253_ = l_Lean_Elab_Tactic_withRWRulesSeq(v___x_4250_, v___x_4252_, v___f_4248_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
lean_dec(v___x_4252_);
return v___x_4253_;
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
v_a_4254_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4242_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4242_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* v_stx_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_Elab_Tactic_evalRewriteSeq(v_stx_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_stx_4262_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4288_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2));
v___x_4290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4291_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
v___x_4292_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4288_, v___x_4289_, v___x_4290_, v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3(){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5));
v___x_4322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6));
v___x_4323_ = l_Lean_addBuiltinDeclarationRanges(v___x_4321_, v___x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
return v_res_4325_;
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
