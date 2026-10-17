// Lean compiler output
// Module: Lean.Elab.Tactic.ElabTerm
// Imports: public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Replace public import Lean.Meta.Tactic.Rename public import Lean.Elab.Tactic.Basic public import Lean.Elab.SyntheticMVars import Lean.Elab.ConfigEval import Lean.Meta.Hint
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_isLetRecAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarKind_isNatural(uint8_t);
lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getLambdaBody(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
lean_object* l_instMonadEIO___redArg();
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
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MVarId_constructorCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "reuse stopped: guard failed at "};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "attempting to close the goal using"};
static const lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\nthis is often due to an occurs-check failure"};
static const lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(181, 27, 253, 38, 166, 91, 92, 173)}};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalExact"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 120, 244, 69, 129, 106, 222)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_refineCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`refine` tactic failed, value"};
static const lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_refineCore___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_refineCore___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "\ndepends on the main goal metavariable `"};
static const lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_refineCore___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_refineCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_refineCore___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRefine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l_Lean_Elab_Tactic_evalRefine___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 66, 166, 159, 104, 233, 32, 227)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRefine"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 145, 22, 71, 20, 173, 227, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(189) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(192) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(189) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(189) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "refine'"};
static const lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 47, 162, 14, 79, 14, 110, 97)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 29, 86, 242, 162, 231, 137, 148)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalRefine'"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 77, 214, 78, 10, 226, 57, 225)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(194) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(197) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(194) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(194) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "`specialize` requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"};
static const lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSpecialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 64, 50, 7, 167, 240, 212, 2)}};
static const lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalSpecialize"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 32, 237, 136, 248, 73, 56, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(199) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(212) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(199) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(199) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabTermForApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Tactic_elabTermForApply___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabTermForApply___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unexpected term `"};
static const lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`; expected single reference to variable"};
static const lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_getFVarIds___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_getFVarIds___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Lean_Elab_Tactic_evalApply___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Lean_Elab_Tactic_evalApply___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalApply"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 174, 163, 187, 9, 67, 156, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(303) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(306) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(303) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(303) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ConstructorConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(97, 249, 41, 57, 31, 122, 146, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig;
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(97, 249, 41, 57, 31, 122, 146, 10)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 74, 180, 42, 194, 193, 172, 110)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_elabConstructorConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " the goal."};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "constructor!"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "Use `constructor!` to apply the first matching constructor without this warning:"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Tactic `constructor` applied constructor `"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "`, but "};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " also "};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matches"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "constructor"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 188, 57, 91, 27, 124, 155, 13)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalConstructor"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 148, 222, 77, 61, 137, 212, 52)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(308) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(312) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(308) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(308) << 1) | 1)),((lean_object*)(((size_t)(68) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value),((lean_object*)(((size_t)(68) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalWithReducible"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 233, 43, 192, 30, 109, 64, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(314) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(315) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(314) << 1) | 1)),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(314) << 1) | 1)),((lean_object*)(((size_t)(72) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value),((lean_object*)(((size_t)(72) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "withReducibleAndInstances"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 231, 54, 217, 251, 49, 216, 49)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "evalWithReducibleAndInstances"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 161, 97, 73, 21, 6, 2, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(317) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(318) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(317) << 1) | 1)),((lean_object*)(((size_t)(67) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(317) << 1) | 1)),((lean_object*)(((size_t)(96) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value),((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value),((lean_object*)(((size_t)(96) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withImplicit"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 55, 151, 94, 210, 189, 147, 133)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalWithImplicit"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 18, 145, 67, 71, 155, 218, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withUnfoldingAll"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 182, 19, 172, 53, 51, 56, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalWithUnfoldingAll"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 149, 127, 27, 154, 31, 88, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(320) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(321) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(320) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(320) << 1) | 1)),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withUnfoldingNone"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 40, 27, 134, 15, 218, 231, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "evalWithUnfoldingNone"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(163, 180, 80, 132, 38, 173, 2, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to find a hypothesis with type"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRename___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rename"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 242, 239, 56, 25, 190, 128, 68)}};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRename___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRename"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 112, 92, 205, 132, 47, 133, 163)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(344) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(359) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(344) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(344) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(lean_object* v_k_1_, uint8_t v_mayPostpone_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_10_ = lean_apply_7(v_k_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, lean_box(0));
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; uint8_t v___x_12_; uint8_t v___x_13_; lean_object* v___x_14_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_10_, 1);
v___x_12_ = l_Lean_Elab_Term_PostponeBehavior_ofBool(v_mayPostpone_2_);
v___x_13_ = 0;
v___x_14_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_12_, v___x_13_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_21_ == 0)
{
lean_object* v_unused_22_; 
v_unused_22_ = lean_ctor_get(v___x_14_, 0);
lean_dec(v_unused_22_);
v___x_16_ = v___x_14_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_dec(v___x_14_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v_a_11_);
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_11_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
lean_dec(v_a_11_);
v_a_23_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_14_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_14_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg___boxed(lean_object* v_k_31_, lean_object* v_mayPostpone_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
uint8_t v_mayPostpone_boxed_40_; lean_object* v_res_41_; 
v_mayPostpone_boxed_40_ = lean_unbox(v_mayPostpone_32_);
v_res_41_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_31_, v_mayPostpone_boxed_40_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(lean_object* v_00_u03b1_42_, lean_object* v_k_43_, uint8_t v_mayPostpone_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_43_, v_mayPostpone_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___boxed(lean_object* v_00_u03b1_53_, lean_object* v_k_54_, lean_object* v_mayPostpone_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
uint8_t v_mayPostpone_boxed_63_; lean_object* v_res_64_; 
v_mayPostpone_boxed_63_ = lean_unbox(v_mayPostpone_55_);
v_res_64_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(v_00_u03b1_53_, v_k_54_, v_mayPostpone_boxed_63_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(lean_object* v_a_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_inc(v___y_67_);
lean_inc_ref(v___y_66_);
v___x_75_ = lean_apply_2(v_a_65_, v___y_66_, v___y_67_);
v___x_76_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_75_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg___boxed(lean_object* v_a_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v_a_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(lean_object* v_00_u03b1_88_, lean_object* v_a_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v_a_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___boxed(lean_object* v_00_u03b1_100_, lean_object* v_a_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(v_00_u03b1_100_, v_a_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(uint8_t v_cond_112_, lean_object* v_____r_113_){
_start:
{
if (v_cond_112_ == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 1;
return v___x_114_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed(lean_object* v_cond_116_, lean_object* v_____r_117_){
_start:
{
uint8_t v_cond_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_cond_boxed_118_ = lean_unbox(v_cond_116_);
v_res_119_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_boxed_118_, v_____r_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(lean_object* v___f_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v___f_121_, v___x_123_);
v___x_125_ = lean_unbox(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed(lean_object* v___f_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(v___f_126_, v_x_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(uint8_t v_cond_138_, lean_object* v_act_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_declName_x3f_149_; lean_object* v_macroStack_150_; uint8_t v_mayPostpone_151_; uint8_t v_errToSorry_152_; lean_object* v_autoBoundImplicitContext_153_; lean_object* v_autoBoundImplicitForbidden_154_; lean_object* v_sectionVars_155_; lean_object* v_sectionFVars_156_; uint8_t v_implicitLambda_157_; uint8_t v_heedElabAsElim_158_; uint8_t v_isNoncomputableSection_159_; uint8_t v_isMetaSection_160_; uint8_t v_ignoreTCFailures_161_; uint8_t v_inPattern_162_; lean_object* v_tacSnap_x3f_163_; uint8_t v_saveRecAppSyntax_164_; uint8_t v_holesAsSyntheticOpaque_165_; uint8_t v_checkDeprecated_166_; lean_object* v_fixedTermElabs_167_; lean_object* v___y_169_; uint8_t v___y_173_; 
v_declName_x3f_149_ = lean_ctor_get(v___y_142_, 0);
v_macroStack_150_ = lean_ctor_get(v___y_142_, 1);
v_mayPostpone_151_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8);
v_errToSorry_152_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_153_ = lean_ctor_get(v___y_142_, 2);
v_autoBoundImplicitForbidden_154_ = lean_ctor_get(v___y_142_, 3);
v_sectionVars_155_ = lean_ctor_get(v___y_142_, 4);
v_sectionFVars_156_ = lean_ctor_get(v___y_142_, 5);
v_implicitLambda_157_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 2);
v_heedElabAsElim_158_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_159_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 4);
v_isMetaSection_160_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_161_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 6);
v_inPattern_162_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_163_ = lean_ctor_get(v___y_142_, 6);
v_saveRecAppSyntax_164_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_165_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 9);
v_checkDeprecated_166_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 10);
v_fixedTermElabs_167_ = lean_ctor_get(v___y_142_, 7);
if (lean_obj_tag(v_tacSnap_x3f_163_) == 0)
{
v___y_169_ = v_tacSnap_x3f_163_;
goto v___jp_168_;
}
else
{
lean_object* v_val_175_; lean_object* v_old_x3f_176_; lean_object* v___x_177_; lean_object* v___f_178_; 
v_val_175_ = lean_ctor_get(v_tacSnap_x3f_163_, 0);
v_old_x3f_176_ = lean_ctor_get(v_val_175_, 0);
v___x_177_ = lean_box(v_cond_138_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_178_, 0, v___x_177_);
if (lean_obj_tag(v_old_x3f_176_) == 1)
{
if (v_cond_138_ == 0)
{
lean_dec_ref(v___f_178_);
goto v___jp_179_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v_map_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_val_182_ = lean_ctor_get(v_old_x3f_176_, 0);
v___x_183_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_146_);
v_map_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_map_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3));
v___x_186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_184_, v___x_185_);
lean_dec(v_map_184_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_dec_ref(v___f_178_);
goto v___jp_179_;
}
else
{
lean_object* v_val_187_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref_known(v___x_186_, 1);
if (lean_obj_tag(v_val_187_) == 1)
{
uint8_t v_v_188_; 
v_v_188_ = lean_ctor_get_uint8(v_val_187_, 0);
lean_dec_ref_known(v_val_187_, 0);
if (v_v_188_ == 0)
{
lean_dec_ref(v___f_178_);
goto v___jp_179_;
}
else
{
lean_object* v_stx_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_stx_189_ = lean_ctor_get(v_val_182_, 0);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_190_, 0, v___f_178_);
v___x_191_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4));
v___x_192_ = lean_box(0);
v___x_193_ = 0;
lean_inc(v_stx_189_);
v___x_194_ = l_Lean_Syntax_formatStx(v_stx_189_, v___x_192_, v___x_193_);
v___x_195_ = l_Std_Format_defWidth;
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l_Std_Format_pretty(v___x_194_, v___x_195_, v___x_196_, v___x_196_);
v___x_198_ = lean_string_append(v___x_191_, v___x_197_);
lean_dec_ref(v___x_197_);
v___x_199_ = lean_dbg_trace(v___x_198_, v___f_190_);
v___x_200_ = lean_unbox(v___x_199_);
lean_dec(v___x_199_);
v___y_173_ = v___x_200_;
goto v___jp_172_;
}
}
else
{
lean_dec(v_val_187_);
lean_dec_ref(v___f_178_);
goto v___jp_179_;
}
}
}
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
lean_dec_ref(v___f_178_);
v___x_201_ = lean_box(0);
v___x_202_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_201_);
v___y_173_ = v___x_202_;
goto v___jp_172_;
}
v___jp_179_:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_180_);
v___y_173_ = v___x_181_;
goto v___jp_172_;
}
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_inc_ref(v_fixedTermElabs_167_);
lean_inc(v_sectionFVars_156_);
lean_inc(v_sectionVars_155_);
lean_inc_ref(v_autoBoundImplicitForbidden_154_);
lean_inc(v_autoBoundImplicitContext_153_);
lean_inc(v_macroStack_150_);
lean_inc(v_declName_x3f_149_);
v___x_170_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_170_, 0, v_declName_x3f_149_);
lean_ctor_set(v___x_170_, 1, v_macroStack_150_);
lean_ctor_set(v___x_170_, 2, v_autoBoundImplicitContext_153_);
lean_ctor_set(v___x_170_, 3, v_autoBoundImplicitForbidden_154_);
lean_ctor_set(v___x_170_, 4, v_sectionVars_155_);
lean_ctor_set(v___x_170_, 5, v_sectionFVars_156_);
lean_ctor_set(v___x_170_, 6, v___y_169_);
lean_ctor_set(v___x_170_, 7, v_fixedTermElabs_167_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8, v_mayPostpone_151_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 1, v_errToSorry_152_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 2, v_implicitLambda_157_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 3, v_heedElabAsElim_158_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 4, v_isNoncomputableSection_159_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 5, v_isMetaSection_160_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 6, v_ignoreTCFailures_161_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 7, v_inPattern_162_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_164_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_165_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*8 + 10, v_checkDeprecated_166_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc(v___y_141_);
lean_inc_ref(v___y_140_);
v___x_171_ = lean_apply_9(v_act_139_, v___y_140_, v___y_141_, v___x_170_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
return v___x_171_;
}
v___jp_172_:
{
if (v___y_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
v___y_169_ = v___x_174_;
goto v___jp_168_;
}
else
{
lean_inc(v_tacSnap_x3f_163_);
v___y_169_ = v_tacSnap_x3f_163_;
goto v___jp_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(lean_object* v_cond_203_, lean_object* v_act_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
uint8_t v_cond_boxed_214_; lean_object* v_res_215_; 
v_cond_boxed_214_ = lean_unbox(v_cond_203_);
v_res_215_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_boxed_214_, v_act_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(lean_object* v_00_u03b1_216_, uint8_t v_cond_217_, lean_object* v_act_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_217_, v_act_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(lean_object* v_00_u03b1_229_, lean_object* v_cond_230_, lean_object* v_act_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_cond_boxed_241_; lean_object* v_res_242_; 
v_cond_boxed_241_ = lean_unbox(v_cond_230_);
v_res_242_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(v_00_u03b1_229_, v_cond_boxed_241_, v_act_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object* v_k_243_, uint8_t v_mayPostpone_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_243_, v_mayPostpone_244_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object* v_k_255_, lean_object* v_mayPostpone_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_mayPostpone_boxed_266_; lean_object* v_res_267_; 
v_mayPostpone_boxed_266_ = lean_unbox(v_mayPostpone_256_);
v_res_267_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(v_k_255_, v_mayPostpone_boxed_266_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object* v___f_268_, lean_object* v_k_269_, uint8_t v_mayPostpone_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
uint8_t v_recover_280_; 
v_recover_280_ = lean_ctor_get_uint8(v___y_271_, sizeof(void*)*1);
if (v_recover_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v_k_269_);
v___x_281_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v___f_268_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; 
lean_dec_ref(v___f_268_);
v___x_282_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_269_, v_mayPostpone_270_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object* v___f_283_, lean_object* v_k_284_, lean_object* v_mayPostpone_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
uint8_t v_mayPostpone_boxed_295_; lean_object* v_res_296_; 
v_mayPostpone_boxed_295_ = lean_unbox(v_mayPostpone_285_);
v_res_296_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(v___f_283_, v_k_284_, v_mayPostpone_boxed_295_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object* v_k_297_, uint8_t v_mayPostpone_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___f_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_308_ = lean_box(v_mayPostpone_298_);
lean_inc_ref(v_k_297_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_309_, 0, v_k_297_);
lean_closure_set(v___f_309_, 1, v___x_308_);
v___x_310_ = lean_box(v_mayPostpone_298_);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_311_, 0, v___f_309_);
lean_closure_set(v___f_311_, 1, v_k_297_);
lean_closure_set(v___f_311_, 2, v___x_310_);
v___x_312_ = 1;
v___x_313_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v___x_312_, v___f_311_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object* v_k_314_, lean_object* v_mayPostpone_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_mayPostpone_boxed_325_; lean_object* v_res_326_; 
v_mayPostpone_boxed_325_ = lean_unbox(v_mayPostpone_315_);
v_res_326_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_314_, v_mayPostpone_boxed_325_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object* v_00_u03b1_327_, lean_object* v_k_328_, uint8_t v_mayPostpone_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_328_, v_mayPostpone_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object* v_00_u03b1_340_, lean_object* v_k_341_, lean_object* v_mayPostpone_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v_mayPostpone_boxed_352_; lean_object* v_res_353_; 
v_mayPostpone_boxed_352_ = lean_unbox(v_mayPostpone_342_);
v_res_353_ = l_Lean_Elab_Tactic_runTermElab(v_00_u03b1_340_, v_k_341_, v_mayPostpone_boxed_352_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(lean_object* v_e_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_Expr_hasMVar(v_e_354_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_e_354_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v_mctx_360_; lean_object* v___x_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_364_; lean_object* v_cache_365_; lean_object* v_zetaDeltaFVarIds_366_; lean_object* v_postponed_367_; lean_object* v_diag_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_377_; 
v___x_359_ = lean_st_ref_get(v___y_355_);
v_mctx_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc_ref(v_mctx_360_);
lean_dec(v___x_359_);
v___x_361_ = l_Lean_instantiateMVarsCore(v_mctx_360_, v_e_354_);
v_fst_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_fst_362_);
v_snd_363_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_snd_363_);
lean_dec_ref(v___x_361_);
v___x_364_ = lean_st_ref_take(v___y_355_);
v_cache_365_ = lean_ctor_get(v___x_364_, 1);
v_zetaDeltaFVarIds_366_ = lean_ctor_get(v___x_364_, 2);
v_postponed_367_ = lean_ctor_get(v___x_364_, 3);
v_diag_368_ = lean_ctor_get(v___x_364_, 4);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_378_);
v___x_370_ = v___x_364_;
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_diag_368_);
lean_inc(v_postponed_367_);
lean_inc(v_zetaDeltaFVarIds_366_);
lean_inc(v_cache_365_);
lean_dec(v___x_364_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_snd_363_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_snd_363_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_cache_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_zetaDeltaFVarIds_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_postponed_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_diag_368_);
v___x_373_ = v_reuseFailAlloc_376_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_st_ref_put(v___y_355_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_fst_362_);
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(lean_object* v_e_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_379_, v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(lean_object* v_e_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_383_, v___y_389_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(lean_object* v_e_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(v_e_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object* v_stx_405_, lean_object* v_expectedType_x3f_406_, uint8_t v_mayPostpone_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_toCold_421_; lean_object* v_currRecDepth_422_; lean_object* v_ref_423_; uint16_t v_optionFlags_424_; uint8_t v_suppressElabErrors_425_; uint8_t v_isRecordingDeps_426_; lean_object* v_ref_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_417_ = 1;
v___x_418_ = lean_box(v___x_417_);
v___x_419_ = lean_box(v___x_417_);
lean_inc(v_stx_405_);
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_420_, 0, v_stx_405_);
lean_closure_set(v___x_420_, 1, v_expectedType_x3f_406_);
lean_closure_set(v___x_420_, 2, v___x_418_);
lean_closure_set(v___x_420_, 3, v___x_419_);
v_toCold_421_ = lean_ctor_get(v_a_414_, 0);
v_currRecDepth_422_ = lean_ctor_get(v_a_414_, 1);
v_ref_423_ = lean_ctor_get(v_a_414_, 2);
v_optionFlags_424_ = lean_ctor_get_uint16(v_a_414_, sizeof(void*)*3);
v_suppressElabErrors_425_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*3 + 2);
v_isRecordingDeps_426_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*3 + 3);
v_ref_427_ = l_Lean_replaceRef(v_stx_405_, v_ref_423_);
lean_dec(v_stx_405_);
lean_inc(v_currRecDepth_422_);
lean_inc_ref(v_toCold_421_);
v___x_428_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_428_, 0, v_toCold_421_);
lean_ctor_set(v___x_428_, 1, v_currRecDepth_422_);
lean_ctor_set(v___x_428_, 2, v_ref_427_);
lean_ctor_set_uint16(v___x_428_, sizeof(void*)*3, v_optionFlags_424_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 2, v_suppressElabErrors_425_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 3, v_isRecordingDeps_426_);
v___x_429_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___x_420_, v_mayPostpone_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v___x_428_, v_a_415_);
lean_dec_ref_known(v___x_428_, 3);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_430_, v_a_413_);
return v___x_431_;
}
else
{
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object* v_stx_432_, lean_object* v_expectedType_x3f_433_, lean_object* v_mayPostpone_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
uint8_t v_mayPostpone_boxed_444_; lean_object* v_res_445_; 
v_mayPostpone_boxed_444_ = lean_unbox(v_mayPostpone_434_);
v_res_445_ = l_Lean_Elab_Tactic_elabTerm(v_stx_432_, v_expectedType_x3f_433_, v_mayPostpone_boxed_444_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object* v_stx_446_, lean_object* v_expectedType_x3f_447_, uint8_t v_mayPostpone_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; 
lean_inc(v_expectedType_x3f_447_);
v___x_458_ = l_Lean_Elab_Tactic_elabTerm(v_stx_446_, v_expectedType_x3f_447_, v_mayPostpone_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
if (lean_obj_tag(v_expectedType_x3f_447_) == 0)
{
return v___x_458_;
}
else
{
lean_object* v_a_459_; lean_object* v_val_460_; lean_object* v___x_461_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_n(v_a_459_, 2);
lean_dec_ref_known(v___x_458_, 1);
v_val_460_ = lean_ctor_get(v_expectedType_x3f_447_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v_expectedType_x3f_447_, 1);
lean_inc(v_a_456_);
lean_inc_ref(v_a_455_);
lean_inc(v_a_454_);
lean_inc_ref(v_a_453_);
v___x_461_ = lean_infer_type(v_a_459_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; uint8_t v_foApprox_464_; uint8_t v_ctxApprox_465_; uint8_t v_quasiPatternApprox_466_; uint8_t v_constApprox_467_; uint8_t v_isDefEqStuckEx_468_; uint8_t v_unificationHints_469_; uint8_t v_proofIrrelevance_470_; uint8_t v_offsetCnstrs_471_; uint8_t v_transparency_472_; uint8_t v_etaStruct_473_; uint8_t v_univApprox_474_; uint8_t v_iota_475_; uint8_t v_beta_476_; uint8_t v_proj_477_; uint8_t v_zeta_478_; uint8_t v_zetaDelta_479_; uint8_t v_zetaUnused_480_; uint8_t v_zetaHave_481_; uint8_t v_canUnfoldPredicateConfig_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_539_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l_Lean_Meta_Context_config(v_a_453_);
v_foApprox_464_ = lean_ctor_get_uint8(v___x_463_, 0);
v_ctxApprox_465_ = lean_ctor_get_uint8(v___x_463_, 1);
v_quasiPatternApprox_466_ = lean_ctor_get_uint8(v___x_463_, 2);
v_constApprox_467_ = lean_ctor_get_uint8(v___x_463_, 3);
v_isDefEqStuckEx_468_ = lean_ctor_get_uint8(v___x_463_, 4);
v_unificationHints_469_ = lean_ctor_get_uint8(v___x_463_, 5);
v_proofIrrelevance_470_ = lean_ctor_get_uint8(v___x_463_, 6);
v_offsetCnstrs_471_ = lean_ctor_get_uint8(v___x_463_, 8);
v_transparency_472_ = lean_ctor_get_uint8(v___x_463_, 9);
v_etaStruct_473_ = lean_ctor_get_uint8(v___x_463_, 10);
v_univApprox_474_ = lean_ctor_get_uint8(v___x_463_, 11);
v_iota_475_ = lean_ctor_get_uint8(v___x_463_, 12);
v_beta_476_ = lean_ctor_get_uint8(v___x_463_, 13);
v_proj_477_ = lean_ctor_get_uint8(v___x_463_, 14);
v_zeta_478_ = lean_ctor_get_uint8(v___x_463_, 15);
v_zetaDelta_479_ = lean_ctor_get_uint8(v___x_463_, 16);
v_zetaUnused_480_ = lean_ctor_get_uint8(v___x_463_, 17);
v_zetaHave_481_ = lean_ctor_get_uint8(v___x_463_, 18);
v_canUnfoldPredicateConfig_482_ = lean_ctor_get_uint8(v___x_463_, 19);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_539_ == 0)
{
v___x_484_ = v___x_463_;
v_isShared_485_ = v_isSharedCheck_539_;
goto v_resetjp_483_;
}
else
{
lean_dec(v___x_463_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_539_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v_trackZetaDelta_486_; lean_object* v_zetaDeltaSet_487_; lean_object* v_lctx_488_; lean_object* v_localInstances_489_; lean_object* v_defEqCtx_x3f_490_; lean_object* v_synthPendingDepth_491_; lean_object* v_customCanUnfoldPredicate_x3f_492_; uint8_t v_univApprox_493_; uint8_t v_inTypeClassResolution_494_; uint8_t v_cacheInferType_495_; uint8_t v___x_496_; lean_object* v___x_498_; 
v_trackZetaDelta_486_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7);
v_zetaDeltaSet_487_ = lean_ctor_get(v_a_453_, 1);
v_lctx_488_ = lean_ctor_get(v_a_453_, 2);
v_localInstances_489_ = lean_ctor_get(v_a_453_, 3);
v_defEqCtx_x3f_490_ = lean_ctor_get(v_a_453_, 4);
v_synthPendingDepth_491_ = lean_ctor_get(v_a_453_, 5);
v_customCanUnfoldPredicate_x3f_492_ = lean_ctor_get(v_a_453_, 6);
v_univApprox_493_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_494_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7 + 2);
v_cacheInferType_495_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7 + 3);
v___x_496_ = 1;
if (v_isShared_485_ == 0)
{
v___x_498_ = v___x_484_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 0, v_foApprox_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 1, v_ctxApprox_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 2, v_quasiPatternApprox_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 3, v_constApprox_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 4, v_isDefEqStuckEx_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 5, v_unificationHints_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 6, v_proofIrrelevance_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 8, v_offsetCnstrs_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 9, v_transparency_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 10, v_etaStruct_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 11, v_univApprox_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 12, v_iota_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 13, v_beta_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 14, v_proj_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 15, v_zeta_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 16, v_zetaDelta_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 17, v_zetaUnused_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 18, v_zetaHave_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 19, v_canUnfoldPredicateConfig_482_);
v___x_498_ = v_reuseFailAlloc_538_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
uint64_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_ctor_set_uint8(v___x_498_, 7, v___x_496_);
v___x_499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint64(v___x_500_, sizeof(void*)*1, v___x_499_);
lean_inc(v_customCanUnfoldPredicate_x3f_492_);
lean_inc(v_synthPendingDepth_491_);
lean_inc(v_defEqCtx_x3f_490_);
lean_inc_ref(v_localInstances_489_);
lean_inc_ref(v_lctx_488_);
lean_inc(v_zetaDeltaSet_487_);
v___x_501_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v_zetaDeltaSet_487_);
lean_ctor_set(v___x_501_, 2, v_lctx_488_);
lean_ctor_set(v___x_501_, 3, v_localInstances_489_);
lean_ctor_set(v___x_501_, 4, v_defEqCtx_x3f_490_);
lean_ctor_set(v___x_501_, 5, v_synthPendingDepth_491_);
lean_ctor_set(v___x_501_, 6, v_customCanUnfoldPredicate_x3f_492_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7, v_trackZetaDelta_486_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7 + 1, v_univApprox_493_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7 + 2, v_inTypeClassResolution_494_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7 + 3, v_cacheInferType_495_);
lean_inc(v_val_460_);
lean_inc(v_a_462_);
v___x_502_ = l_Lean_Meta_isExprDefEq(v_a_462_, v_val_460_, v___x_501_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref_known(v___x_501_, 7);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_529_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_529_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_529_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_529_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; 
v___x_507_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_del_object(v___x_505_);
v___x_508_ = lean_box(0);
lean_inc(v_a_459_);
v___x_509_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_508_, v_val_460_, v_a_462_, v_a_459_, v___x_508_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_509_, 0);
lean_dec(v_unused_517_);
v___x_511_ = v___x_509_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_dec(v___x_509_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v_a_459_);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_459_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_459_);
v_a_518_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_509_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_509_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v___x_527_; 
lean_dec(v_a_462_);
lean_dec(v_val_460_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_a_459_);
v___x_527_ = v___x_505_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_459_);
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
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_a_462_);
lean_dec(v_val_460_);
lean_dec(v_a_459_);
v_a_530_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_502_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_502_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
else
{
lean_dec(v_val_460_);
lean_dec(v_a_459_);
return v___x_461_;
}
}
}
else
{
lean_dec(v_expectedType_x3f_447_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* v_stx_540_, lean_object* v_expectedType_x3f_541_, lean_object* v_mayPostpone_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
uint8_t v_mayPostpone_boxed_552_; lean_object* v_res_553_; 
v_mayPostpone_boxed_552_ = lean_unbox(v_mayPostpone_542_);
v_res_553_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_stx_540_, v_expectedType_x3f_541_, v_mayPostpone_boxed_552_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_553_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_Elab_abortTacticExceptionId;
v___x_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object* v_00_u03b1_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object* v_00_u03b1_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(v_00_u03b1_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object* v_mvarIds_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(0);
v___x_595_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_mvarIds_584_, v___x_594_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_606_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_601_);
v___x_603_ = v___x_598_;
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
else
{
lean_object* v___x_605_; 
lean_del_object(v___x_598_);
v___x_605_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_605_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_595_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_595_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* v_mvarIds_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_mvarIds_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec_ref(v_mvarIds_615_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object* v___x_626_, lean_object* v_mvarCounterSaved_627_, lean_object* v_as_628_, size_t v_i_629_, size_t v_stop_630_, lean_object* v_b_631_){
_start:
{
lean_object* v___y_633_; uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_eq(v_i_629_, v_stop_630_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_index_640_; uint8_t v___x_641_; 
v___x_638_ = lean_array_uget_borrowed(v_as_628_, v_i_629_);
lean_inc(v___x_638_);
v___x_639_ = l_Lean_MetavarContext_getDecl(v___x_626_, v___x_638_);
v_index_640_ = lean_ctor_get(v___x_639_, 6);
lean_inc(v_index_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = lean_nat_dec_le(v_mvarCounterSaved_627_, v_index_640_);
lean_dec(v_index_640_);
if (v___x_641_ == 0)
{
v___y_633_ = v_b_631_;
goto v___jp_632_;
}
else
{
lean_object* v___x_642_; 
lean_inc(v___x_638_);
v___x_642_ = lean_array_push(v_b_631_, v___x_638_);
v___y_633_ = v___x_642_;
goto v___jp_632_;
}
}
else
{
return v_b_631_;
}
v___jp_632_:
{
size_t v___x_634_; size_t v___x_635_; 
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_629_, v___x_634_);
v_i_629_ = v___x_635_;
v_b_631_ = v___y_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object* v___x_643_, lean_object* v_mvarCounterSaved_644_, lean_object* v_as_645_, lean_object* v_i_646_, lean_object* v_stop_647_, lean_object* v_b_648_){
_start:
{
size_t v_i_boxed_649_; size_t v_stop_boxed_650_; lean_object* v_res_651_; 
v_i_boxed_649_ = lean_unbox_usize(v_i_646_);
lean_dec(v_i_646_);
v_stop_boxed_650_ = lean_unbox_usize(v_stop_647_);
lean_dec(v_stop_647_);
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v___x_643_, v_mvarCounterSaved_644_, v_as_645_, v_i_boxed_649_, v_stop_boxed_650_, v_b_648_);
lean_dec_ref(v_as_645_);
lean_dec(v_mvarCounterSaved_644_);
lean_dec_ref(v___x_643_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object* v_mvarIds_654_, lean_object* v_mvarCounterSaved_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_658_ = lean_st_ref_get(v_a_656_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_array_get_size(v_mvarIds_654_);
v___x_661_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_662_ = lean_nat_dec_lt(v___x_659_, v___x_660_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v___x_658_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
return v___x_663_;
}
else
{
lean_object* v_mctx_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_mctx_664_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_mctx_664_);
lean_dec(v___x_658_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = lean_usize_of_nat(v___x_660_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_664_, v_mvarCounterSaved_655_, v_mvarIds_654_, v___x_665_, v___x_666_, v___x_661_);
lean_dec_ref(v_mctx_664_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object* v_mvarIds_669_, lean_object* v_mvarCounterSaved_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_669_, v_mvarCounterSaved_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec(v_mvarCounterSaved_670_);
lean_dec_ref(v_mvarIds_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* v_mvarIds_674_, lean_object* v_mvarCounterSaved_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_674_, v_mvarCounterSaved_675_, v_a_677_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* v_mvarIds_682_, lean_object* v_mvarCounterSaved_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Elab_Tactic_filterOldMVars(v_mvarIds_682_, v_mvarCounterSaved_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_mvarCounterSaved_683_);
lean_dec_ref(v_mvarIds_682_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; 
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
v___x_700_ = lean_apply_9(v_x_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, lean_box(0));
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(v_x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object* v_mvarId_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___f_723_; lean_object* v___x_724_; 
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
v___f_723_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_723_, 0, v_x_713_);
lean_closure_set(v___f_723_, 1, v___y_714_);
lean_closure_set(v___f_723_, 2, v___y_715_);
lean_closure_set(v___f_723_, 3, v___y_716_);
lean_closure_set(v___f_723_, 4, v___y_717_);
v___x_724_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_712_, v___f_723_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
return v___x_724_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object* v_mvarId_733_, lean_object* v_x_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_733_, v_x_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object* v_00_u03b1_745_, lean_object* v_mvarId_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_746_, v_x_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object* v_00_u03b1_758_, lean_object* v_mvarId_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(v_00_u03b1_758_, v_mvarId_759_, v_x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_770_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object* v_a_777_, lean_object* v_x_778_, lean_object* v_tacName_779_, uint8_t v_checkNewUnassigned_780_, lean_object* v_mvarCounter_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
lean_inc(v_a_777_);
v___x_791_ = l_Lean_MVarId_getType(v_a_777_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
lean_inc(v_a_777_);
v___x_793_ = l_Lean_MVarId_getTag(v_a_777_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
v___x_795_ = lean_apply_11(v_x_778_, v_a_792_, v_a_794_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, lean_box(0));
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
if (v_checkNewUnassigned_780_ == 0)
{
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
v___y_798_ = v___y_786_;
v___y_799_ = v___y_787_;
v___y_800_ = v___y_788_;
v___y_801_ = v___y_789_;
goto v___jp_797_;
}
else
{
lean_object* v___x_828_; 
lean_inc(v_a_796_);
v___x_828_ = l_Lean_Meta_getMVars(v_a_796_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
v___x_830_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_829_, v_mvarCounter_781_, v___y_787_);
lean_dec(v_a_829_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_831_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v_a_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref_known(v___x_832_, 1);
v___y_798_ = v___y_786_;
v___y_799_ = v___y_787_;
v___y_800_ = v___y_788_;
v___y_801_ = v___y_789_;
goto v___jp_797_;
}
else
{
lean_dec(v_a_796_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v_tacName_779_);
lean_dec(v_a_777_);
return v___x_832_;
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_796_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v_tacName_779_);
lean_dec(v_a_777_);
v_a_833_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_828_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_828_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
v___jp_797_:
{
lean_object* v___x_802_; 
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v_a_796_);
lean_inc(v_a_777_);
v___x_802_ = lean_checked_assign(v_a_777_, v_a_796_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_819_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_819_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_805_);
v___x_808_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1);
v___x_809_ = l_Lean_indentExpr(v_a_796_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = l_Lean_Meta_throwTacticEx___redArg(v_tacName_779_, v_a_777_, v___x_813_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_a_796_);
lean_dec(v_tacName_779_);
lean_dec(v_a_777_);
v___x_815_ = lean_box(0);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_817_ = v___x_805_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_a_796_);
lean_dec(v_tacName_779_);
lean_dec(v_a_777_);
v_a_820_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_802_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_802_);
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
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v_tacName_779_);
lean_dec(v_a_777_);
v_a_841_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_795_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_795_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_a_792_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v_tacName_779_);
lean_dec_ref(v_x_778_);
lean_dec(v_a_777_);
v_a_849_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_793_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_793_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v_tacName_779_);
lean_dec_ref(v_x_778_);
lean_dec(v_a_777_);
v_a_857_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_791_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_791_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object* v_a_865_, lean_object* v_x_866_, lean_object* v_tacName_867_, lean_object* v_checkNewUnassigned_868_, lean_object* v_mvarCounter_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_879_; lean_object* v_res_880_; 
v_checkNewUnassigned_boxed_879_ = lean_unbox(v_checkNewUnassigned_868_);
v_res_880_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(v_a_865_, v_x_866_, v_tacName_867_, v_checkNewUnassigned_boxed_879_, v_mvarCounter_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v_mvarCounter_869_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* v_tacName_881_, lean_object* v_x_882_, uint8_t v_checkNewUnassigned_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; lean_object* v_mctx_894_; lean_object* v_mvarCounter_895_; lean_object* v___x_896_; 
v___x_893_ = lean_st_ref_get(v_a_889_);
v_mctx_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc_ref(v_mctx_894_);
lean_dec(v___x_893_);
v_mvarCounter_895_ = lean_ctor_get(v_mctx_894_, 3);
lean_inc(v_mvarCounter_895_);
lean_dec_ref(v_mctx_894_);
v___x_896_ = l_Lean_Elab_Tactic_popMainGoal___redArg(v_a_885_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___f_899_; lean_object* v___x_900_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_n(v_a_897_, 3);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = lean_box(v_checkNewUnassigned_883_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed), 14, 5);
lean_closure_set(v___f_899_, 0, v_a_897_);
lean_closure_set(v___f_899_, 1, v_x_882_);
lean_closure_set(v___f_899_, 2, v_tacName_881_);
lean_closure_set(v___f_899_, 3, v___x_898_);
lean_closure_set(v___f_899_, 4, v_mvarCounter_895_);
v___x_900_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_a_897_, v___f_899_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_dec(v_a_897_);
return v___x_900_;
}
else
{
lean_object* v_a_901_; uint8_t v___x_902_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v___x_902_ = l_Lean_Exception_isInterrupt(v_a_901_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; 
lean_inc(v_a_901_);
v___x_903_ = l_Lean_Exception_isRuntime(v_a_901_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_904_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_897_, v_a_885_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_912_);
v___x_906_ = v___x_904_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_dec(v___x_904_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 1);
lean_ctor_set(v___x_906_, 0, v_a_901_);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_901_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_dec(v_a_901_);
return v___x_904_;
}
}
else
{
lean_dec(v_a_897_);
return v___x_900_;
}
}
else
{
lean_dec(v_a_897_);
return v___x_900_;
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_mvarCounter_895_);
lean_dec_ref(v_x_882_);
lean_dec(v_tacName_881_);
v_a_913_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_896_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_896_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* v_tacName_921_, lean_object* v_x_922_, lean_object* v_checkNewUnassigned_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_933_; lean_object* v_res_934_; 
v_checkNewUnassigned_boxed_933_ = lean_unbox(v_checkNewUnassigned_923_);
v_res_934_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacName_921_, v_x_922_, v_checkNewUnassigned_boxed_933_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_934_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_box(0);
v___x_936_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0);
v___x_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object* v_00_u03b1_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object* v_00_u03b1_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(v_00_u03b1_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object* v___x_965_, lean_object* v_type_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v_type_966_);
v___x_978_ = 0;
v___x_979_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_965_, v___x_977_, v___x_978_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object* v___x_980_, lean_object* v_type_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Elab_Tactic_evalExact___lam__0(v___x_980_, v_type_981_, v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v_x_982_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* v_stx_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
lean_inc(v_stx_1004_);
v___x_1015_ = l_Lean_Syntax_isOfKind(v_stx_1004_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_dec(v_stx_1004_);
v___x_1016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = l_Lean_Syntax_getArg(v_stx_1004_, v___x_1017_);
lean_dec(v_stx_1004_);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1019_, 0, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__5));
v___x_1021_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_1020_, v___f_1019_, v___x_1015_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object* v_stx_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Elab_Tactic_evalExact(v_stx_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1040_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
v___x_1042_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1043_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___boxed), 10, 0);
v___x_1044_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1040_, v___x_1041_, v___x_1042_, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6));
v___x_1075_ = l_Lean_addBuiltinDeclarationRanges(v___x_1073_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
return v_res_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object* v_mctx_1078_, lean_object* v_mvarId_u2081_1079_, lean_object* v_mvarId_u2082_1080_){
_start:
{
lean_object* v_decl_u2081_1081_; lean_object* v_index_1082_; lean_object* v_decl_u2082_1083_; lean_object* v_index_1084_; uint8_t v___x_1085_; 
lean_inc(v_mvarId_u2081_1079_);
v_decl_u2081_1081_ = l_Lean_MetavarContext_getDecl(v_mctx_1078_, v_mvarId_u2081_1079_);
v_index_1082_ = lean_ctor_get(v_decl_u2081_1081_, 6);
lean_inc(v_index_1082_);
lean_dec_ref(v_decl_u2081_1081_);
lean_inc(v_mvarId_u2082_1080_);
v_decl_u2082_1083_ = l_Lean_MetavarContext_getDecl(v_mctx_1078_, v_mvarId_u2082_1080_);
v_index_1084_ = lean_ctor_get(v_decl_u2082_1083_, 6);
lean_inc(v_index_1084_);
lean_dec_ref(v_decl_u2082_1083_);
v___x_1085_ = lean_nat_dec_eq(v_index_1082_, v_index_1084_);
if (v___x_1085_ == 0)
{
uint8_t v___x_1086_; 
lean_dec(v_mvarId_u2082_1080_);
lean_dec(v_mvarId_u2081_1079_);
v___x_1086_ = lean_nat_dec_lt(v_index_1082_, v_index_1084_);
lean_dec(v_index_1084_);
lean_dec(v_index_1082_);
return v___x_1086_;
}
else
{
uint8_t v___x_1087_; 
lean_dec(v_index_1084_);
lean_dec(v_index_1082_);
v___x_1087_ = l_Lean_Name_quickLt(v_mvarId_u2081_1079_, v_mvarId_u2082_1080_);
lean_dec(v_mvarId_u2082_1080_);
lean_dec(v_mvarId_u2081_1079_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object* v_mctx_1088_, lean_object* v_mvarId_u2081_1089_, lean_object* v_mvarId_u2082_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(v_mctx_1088_, v_mvarId_u2081_1089_, v_mvarId_u2082_1090_);
lean_dec_ref(v_mctx_1088_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object* v_mvarIds_1093_, lean_object* v_toPure_1094_, lean_object* v_mctx_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_array_get_size(v_mvarIds_1093_);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_nat_dec_eq(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___f_1099_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; uint8_t v___x_1110_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1099_, 0, v_mctx_1095_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_sub(v___x_1096_, v___x_1105_);
v___x_1110_ = lean_nat_dec_le(v___x_1097_, v___x_1106_);
if (v___x_1110_ == 0)
{
lean_inc(v___x_1106_);
v___y_1108_ = v___x_1106_;
goto v___jp_1107_;
}
else
{
v___y_1108_ = v___x_1097_;
goto v___jp_1107_;
}
v___jp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1099_, v___x_1096_, v_mvarIds_1093_, v___y_1101_, v___y_1102_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1102_);
v___x_1104_ = lean_apply_2(v_toPure_1094_, lean_box(0), v___x_1103_);
return v___x_1104_;
}
v___jp_1107_:
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_le(v___y_1108_, v___x_1106_);
if (v___x_1109_ == 0)
{
lean_dec(v___x_1106_);
lean_inc(v___y_1108_);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v___y_1108_;
goto v___jp_1100_;
}
else
{
v___y_1101_ = v___y_1108_;
v___y_1102_ = v___x_1106_;
goto v___jp_1100_;
}
}
}
else
{
lean_object* v___x_1111_; 
lean_dec_ref(v_mctx_1095_);
v___x_1111_ = lean_apply_2(v_toPure_1094_, lean_box(0), v_mvarIds_1093_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_mvarIds_1114_){
_start:
{
lean_object* v_toApplicative_1115_; lean_object* v_toBind_1116_; lean_object* v_getMCtx_1117_; lean_object* v_toPure_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
v_toApplicative_1115_ = lean_ctor_get(v_inst_1113_, 0);
lean_inc_ref(v_toApplicative_1115_);
v_toBind_1116_ = lean_ctor_get(v_inst_1113_, 1);
lean_inc(v_toBind_1116_);
lean_dec_ref(v_inst_1113_);
v_getMCtx_1117_ = lean_ctor_get(v_inst_1112_, 0);
lean_inc(v_getMCtx_1117_);
lean_dec_ref(v_inst_1112_);
v_toPure_1118_ = lean_ctor_get(v_toApplicative_1115_, 1);
lean_inc(v_toPure_1118_);
lean_dec_ref(v_toApplicative_1115_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1119_, 0, v_mvarIds_1114_);
lean_closure_set(v___f_1119_, 1, v_toPure_1118_);
v___x_1120_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v_getMCtx_1117_, v___f_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_mvarIds_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1122_, v_inst_1123_, v_mvarIds_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_mvarIds_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1126_, v_inst_1127_, v_mvarIds_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* v_m_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_mvarIds_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1131_, v_inst_1132_, v_mvarIds_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_mctx_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_st_ref_get(v___y_1136_);
v_mctx_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_mctx_1141_);
lean_dec(v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_mctx_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object* v_val_1149_, lean_object* v_toPure_1150_, lean_object* v_newMVarIds_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_val_1149_);
lean_ctor_set(v___x_1152_, 1, v_newMVarIds_1151_);
v___x_1153_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v_inst_1156_, lean_object* v_toBind_1157_, lean_object* v___f_1158_, lean_object* v_newMVarIds_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v___x_1154_, v___x_1155_, v_newMVarIds_1159_);
v___x_1161_ = lean_apply_2(v_inst_1156_, lean_box(0), v___x_1160_);
v___x_1162_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1161_, v___f_1158_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object* v_mvarCounter_1163_, lean_object* v_inst_1164_, lean_object* v_toBind_1165_, lean_object* v___f_1166_, lean_object* v_newMVarIds_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_filterOldMVars___boxed), 7, 2);
lean_closure_set(v___x_1168_, 0, v_newMVarIds_1167_);
lean_closure_set(v___x_1168_, 1, v_mvarCounter_1163_);
v___x_1169_ = lean_apply_2(v_inst_1164_, lean_box(0), v___x_1168_);
v___x_1170_ = lean_apply_4(v_toBind_1165_, lean_box(0), lean_box(0), v___x_1169_, v___f_1166_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object* v_toPure_1171_, lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_inst_1174_, lean_object* v_toBind_1175_, lean_object* v_mvarCounter_1176_, lean_object* v_val_1177_){
_start:
{
lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_val_1177_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1178_, 0, v_val_1177_);
lean_closure_set(v___f_1178_, 1, v_toPure_1171_);
lean_inc_n(v_toBind_1175_, 2);
lean_inc_n(v_inst_1174_, 2);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1179_, 0, v___x_1172_);
lean_closure_set(v___f_1179_, 1, v___x_1173_);
lean_closure_set(v___f_1179_, 2, v_inst_1174_);
lean_closure_set(v___f_1179_, 3, v_toBind_1175_);
lean_closure_set(v___f_1179_, 4, v___f_1178_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1180_, 0, v_mvarCounter_1176_);
lean_closure_set(v___f_1180_, 1, v_inst_1174_);
lean_closure_set(v___f_1180_, 2, v_toBind_1175_);
lean_closure_set(v___f_1180_, 3, v___f_1179_);
v___x_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_getMVarsNoDelayed___boxed), 6, 1);
lean_closure_set(v___x_1181_, 0, v_val_1177_);
v___x_1182_ = lean_apply_2(v_inst_1174_, lean_box(0), v___x_1181_);
v___x_1183_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v___x_1182_, v___f_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object* v_toPure_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_inst_1187_, lean_object* v_toBind_1188_, lean_object* v_k_1189_, lean_object* v_____do__lift_1190_){
_start:
{
lean_object* v_mvarCounter_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; 
v_mvarCounter_1191_ = lean_ctor_get(v_____do__lift_1190_, 3);
lean_inc(v_mvarCounter_1191_);
lean_dec_ref(v_____do__lift_1190_);
lean_inc(v_toBind_1188_);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1192_, 0, v_toPure_1184_);
lean_closure_set(v___f_1192_, 1, v___x_1185_);
lean_closure_set(v___f_1192_, 2, v___x_1186_);
lean_closure_set(v___f_1192_, 3, v_inst_1187_);
lean_closure_set(v___f_1192_, 4, v_toBind_1188_);
lean_closure_set(v___f_1192_, 5, v_mvarCounter_1191_);
v___x_1193_ = lean_apply_4(v_toBind_1188_, lean_box(0), lean_box(0), v_k_1189_, v___f_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_instMonadEIO___redArg();
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0);
v___x_1196_ = l_StateRefT_x27_instMonad___redArg(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_toApplicative_1207_; lean_object* v_toFunctor_1208_; lean_object* v_toSeq_1209_; lean_object* v_toSeqLeft_1210_; lean_object* v_toSeqRight_1211_; lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_toApplicative_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1257_; 
v___x_1205_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_1206_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1);
v_toApplicative_1207_ = lean_ctor_get(v___x_1206_, 0);
v_toFunctor_1208_ = lean_ctor_get(v_toApplicative_1207_, 0);
v_toSeq_1209_ = lean_ctor_get(v_toApplicative_1207_, 2);
v_toSeqLeft_1210_ = lean_ctor_get(v_toApplicative_1207_, 3);
v_toSeqRight_1211_ = lean_ctor_get(v_toApplicative_1207_, 4);
v___f_1212_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2));
v___f_1213_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1208_, 2);
v___f_1214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1214_, 0, v_toFunctor_1208_);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toFunctor_1208_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___f_1214_);
lean_ctor_set(v___x_1216_, 1, v___f_1215_);
lean_inc(v_toSeqRight_1211_);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toSeqRight_1211_);
lean_inc(v_toSeqLeft_1210_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toSeqLeft_1210_);
lean_inc(v_toSeq_1209_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeq_1209_);
v___x_1220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1216_);
lean_ctor_set(v___x_1220_, 1, v___f_1212_);
lean_ctor_set(v___x_1220_, 2, v___f_1219_);
lean_ctor_set(v___x_1220_, 3, v___f_1218_);
lean_ctor_set(v___x_1220_, 4, v___f_1217_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___f_1213_);
v___x_1222_ = l_StateRefT_x27_instMonad___redArg(v___x_1221_);
v_toApplicative_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1222_, 1);
lean_dec(v_unused_1258_);
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1257_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_toApplicative_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1257_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_toFunctor_1227_; lean_object* v_toSeq_1228_; lean_object* v_toSeqLeft_1229_; lean_object* v_toSeqRight_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1255_; 
v_toFunctor_1227_ = lean_ctor_get(v_toApplicative_1223_, 0);
v_toSeq_1228_ = lean_ctor_get(v_toApplicative_1223_, 2);
v_toSeqLeft_1229_ = lean_ctor_get(v_toApplicative_1223_, 3);
v_toSeqRight_1230_ = lean_ctor_get(v_toApplicative_1223_, 4);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_toApplicative_1223_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v_toApplicative_1223_, 1);
lean_dec(v_unused_1256_);
v___x_1232_ = v_toApplicative_1223_;
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_toSeqRight_1230_);
lean_inc(v_toSeqLeft_1229_);
lean_inc(v_toSeq_1228_);
lean_inc(v_toFunctor_1227_);
lean_dec(v_toApplicative_1223_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___x_1243_; 
v___f_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4));
v___f_1235_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_1227_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toFunctor_1227_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toFunctor_1227_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___f_1236_);
lean_ctor_set(v___x_1238_, 1, v___f_1237_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toSeqRight_1230_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeqLeft_1229_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toSeq_1228_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 4, v___f_1239_);
lean_ctor_set(v___x_1232_, 3, v___f_1240_);
lean_ctor_set(v___x_1232_, 2, v___f_1241_);
lean_ctor_set(v___x_1232_, 1, v___f_1234_);
lean_ctor_set(v___x_1232_, 0, v___x_1238_);
v___x_1243_ = v___x_1232_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___f_1234_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v___f_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v___f_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v___f_1239_);
v___x_1243_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v___f_1235_);
lean_ctor_set(v___x_1225_, 0, v___x_1243_);
v___x_1245_ = v___x_1225_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___f_1235_);
v___x_1245_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v_toApplicative_1246_; lean_object* v_toBind_1247_; lean_object* v_toPure_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; 
v_toApplicative_1246_ = lean_ctor_get(v_inst_1202_, 0);
lean_inc_ref(v_toApplicative_1246_);
v_toBind_1247_ = lean_ctor_get(v_inst_1202_, 1);
lean_inc_n(v_toBind_1247_, 2);
lean_dec_ref(v_inst_1202_);
v_toPure_1248_ = lean_ctor_get(v_toApplicative_1246_, 1);
lean_inc(v_toPure_1248_);
lean_dec_ref(v_toApplicative_1246_);
v___f_1249_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6));
lean_inc(v_inst_1203_);
v___x_1250_ = lean_apply_2(v_inst_1203_, lean_box(0), v___f_1249_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5), 7, 6);
lean_closure_set(v___f_1251_, 0, v_toPure_1248_);
lean_closure_set(v___f_1251_, 1, v___x_1205_);
lean_closure_set(v___f_1251_, 2, v___x_1245_);
lean_closure_set(v___f_1251_, 3, v_inst_1203_);
lean_closure_set(v___f_1251_, 4, v_toBind_1247_);
lean_closure_set(v___f_1251_, 5, v_k_1204_);
v___x_1252_ = lean_apply_4(v_toBind_1247_, lean_box(0), lean_box(0), v___x_1250_, v___f_1251_);
return v___x_1252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object* v_m_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_k_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg(v_inst_1260_, v_inst_1261_, v_k_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object* v_as_1264_, size_t v_i_1265_, size_t v_stop_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_a_1276_; uint8_t v___x_1280_; 
v___x_1280_ = lean_usize_dec_eq(v_i_1265_, v_stop_1266_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_array_uget_borrowed(v_as_1264_, v_i_1265_);
lean_inc(v___x_1281_);
v___x_1282_ = l_Lean_Elab_Term_isLetRecAuxMVar(v___x_1281_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; uint8_t v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = lean_unbox(v_a_1283_);
lean_dec(v_a_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_inc(v___x_1281_);
v___x_1285_ = lean_array_push(v_b_1267_, v___x_1281_);
v_a_1276_ = v___x_1285_;
goto v___jp_1275_;
}
else
{
v_a_1276_ = v_b_1267_;
goto v___jp_1275_;
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_b_1267_);
v_a_1286_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1282_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1282_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_b_1267_);
return v___x_1294_;
}
v___jp_1275_:
{
size_t v___x_1277_; size_t v___x_1278_; 
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_add(v_i_1265_, v___x_1277_);
v_i_1265_ = v___x_1278_;
v_b_1267_ = v_a_1276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object* v_as_1295_, lean_object* v_i_1296_, lean_object* v_stop_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
size_t v_i_boxed_1306_; size_t v_stop_boxed_1307_; lean_object* v_res_1308_; 
v_i_boxed_1306_ = lean_unbox_usize(v_i_1296_);
lean_dec(v_i_1296_);
v_stop_boxed_1307_ = lean_unbox_usize(v_stop_1297_);
lean_dec(v_stop_1297_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1295_, v_i_boxed_1306_, v_stop_boxed_1307_, v_b_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec_ref(v_as_1295_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object* v_as_1309_, size_t v_i_1310_, size_t v_stop_1311_, lean_object* v_b_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_a_1319_; uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_eq(v_i_1310_, v_stop_1311_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_array_uget_borrowed(v_as_1309_, v_i_1310_);
lean_inc(v___x_1324_);
v___x_1325_ = l_Lean_MVarId_getKind(v___x_1324_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; uint8_t v___x_1327_; uint8_t v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_unbox(v_a_1326_);
lean_dec(v_a_1326_);
v___x_1328_ = l_Lean_MetavarKind_isNatural(v___x_1327_);
if (v___x_1328_ == 0)
{
v_a_1319_ = v_b_1312_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1329_; 
lean_inc(v___x_1324_);
v___x_1329_ = lean_array_push(v_b_1312_, v___x_1324_);
v_a_1319_ = v___x_1329_;
goto v___jp_1318_;
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_b_1312_);
v_a_1330_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1325_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_b_1312_);
return v___x_1338_;
}
v___jp_1318_:
{
size_t v___x_1320_; size_t v___x_1321_; 
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1310_, v___x_1320_);
v_i_1310_ = v___x_1321_;
v_b_1312_ = v_a_1319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object* v_as_1339_, lean_object* v_i_1340_, lean_object* v_stop_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
size_t v_i_boxed_1348_; size_t v_stop_boxed_1349_; lean_object* v_res_1350_; 
v_i_boxed_1348_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_stop_boxed_1349_ = lean_unbox_usize(v_stop_1341_);
lean_dec(v_stop_1341_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1339_, v_i_boxed_1348_, v_stop_boxed_1349_, v_b_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec_ref(v_as_1339_);
return v_res_1350_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___x_1351_, lean_object* v_mvarId_u2081_1352_, lean_object* v_mvarId_u2082_1353_){
_start:
{
lean_object* v_decl_u2081_1354_; lean_object* v_index_1355_; lean_object* v_decl_u2082_1356_; lean_object* v_index_1357_; uint8_t v___x_1358_; 
lean_inc(v_mvarId_u2081_1352_);
v_decl_u2081_1354_ = l_Lean_MetavarContext_getDecl(v___x_1351_, v_mvarId_u2081_1352_);
v_index_1355_ = lean_ctor_get(v_decl_u2081_1354_, 6);
lean_inc(v_index_1355_);
lean_dec_ref(v_decl_u2081_1354_);
lean_inc(v_mvarId_u2082_1353_);
v_decl_u2082_1356_ = l_Lean_MetavarContext_getDecl(v___x_1351_, v_mvarId_u2082_1353_);
v_index_1357_ = lean_ctor_get(v_decl_u2082_1356_, 6);
lean_inc(v_index_1357_);
lean_dec_ref(v_decl_u2082_1356_);
v___x_1358_ = lean_nat_dec_eq(v_index_1355_, v_index_1357_);
if (v___x_1358_ == 0)
{
uint8_t v___x_1359_; 
lean_dec(v_mvarId_u2082_1353_);
lean_dec(v_mvarId_u2081_1352_);
v___x_1359_ = lean_nat_dec_lt(v_index_1355_, v_index_1357_);
lean_dec(v_index_1357_);
lean_dec(v_index_1355_);
return v___x_1359_;
}
else
{
uint8_t v___x_1360_; 
lean_dec(v_index_1357_);
lean_dec(v_index_1355_);
v___x_1360_ = l_Lean_Name_quickLt(v_mvarId_u2081_1352_, v_mvarId_u2082_1353_);
lean_dec(v_mvarId_u2082_1353_);
lean_dec(v_mvarId_u2081_1352_);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_1361_, lean_object* v_mvarId_u2081_1362_, lean_object* v_mvarId_u2082_1363_){
_start:
{
uint8_t v_res_1364_; lean_object* v_r_1365_; 
v_res_1364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1361_, v_mvarId_u2081_1362_, v_mvarId_u2082_1363_);
lean_dec_ref(v___x_1361_);
v_r_1365_ = lean_box(v_res_1364_);
return v_r_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_1366_, lean_object* v_hi_1367_, lean_object* v_pivot_1368_, lean_object* v_as_1369_, lean_object* v_i_1370_, lean_object* v_k_1371_){
_start:
{
uint8_t v___y_1373_; uint8_t v___x_1382_; 
v___x_1382_ = lean_nat_dec_lt(v_k_1371_, v_hi_1367_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_k_1371_);
lean_dec(v_pivot_1368_);
v___x_1383_ = lean_array_fswap(v_as_1369_, v_i_1370_, v_hi_1367_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_i_1370_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; lean_object* v_decl_u2081_1386_; lean_object* v_index_1387_; lean_object* v_decl_u2082_1388_; lean_object* v_index_1389_; uint8_t v___x_1390_; 
v___x_1385_ = lean_array_fget_borrowed(v_as_1369_, v_k_1371_);
lean_inc(v___x_1385_);
v_decl_u2081_1386_ = l_Lean_MetavarContext_getDecl(v___x_1366_, v___x_1385_);
v_index_1387_ = lean_ctor_get(v_decl_u2081_1386_, 6);
lean_inc(v_index_1387_);
lean_dec_ref(v_decl_u2081_1386_);
lean_inc(v_pivot_1368_);
v_decl_u2082_1388_ = l_Lean_MetavarContext_getDecl(v___x_1366_, v_pivot_1368_);
v_index_1389_ = lean_ctor_get(v_decl_u2082_1388_, 6);
lean_inc(v_index_1389_);
lean_dec_ref(v_decl_u2082_1388_);
v___x_1390_ = lean_nat_dec_eq(v_index_1387_, v_index_1389_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_nat_dec_lt(v_index_1387_, v_index_1389_);
lean_dec(v_index_1389_);
lean_dec(v_index_1387_);
v___y_1373_ = v___x_1391_;
goto v___jp_1372_;
}
else
{
uint8_t v___x_1392_; 
lean_dec(v_index_1389_);
lean_dec(v_index_1387_);
v___x_1392_ = l_Lean_Name_quickLt(v___x_1385_, v_pivot_1368_);
v___y_1373_ = v___x_1392_;
goto v___jp_1372_;
}
}
v___jp_1372_:
{
if (v___y_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_add(v_k_1371_, v___x_1374_);
lean_dec(v_k_1371_);
v_k_1371_ = v___x_1375_;
goto _start;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_array_fswap(v_as_1369_, v_i_1370_, v_k_1371_);
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_add(v_i_1370_, v___x_1378_);
lean_dec(v_i_1370_);
v___x_1380_ = lean_nat_add(v_k_1371_, v___x_1378_);
lean_dec(v_k_1371_);
v_as_1369_ = v___x_1377_;
v_i_1370_ = v___x_1379_;
v_k_1371_ = v___x_1380_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_1393_, lean_object* v_hi_1394_, lean_object* v_pivot_1395_, lean_object* v_as_1396_, lean_object* v_i_1397_, lean_object* v_k_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1393_, v_hi_1394_, v_pivot_1395_, v_as_1396_, v_i_1397_, v_k_1398_);
lean_dec(v_hi_1394_);
lean_dec_ref(v___x_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object* v___x_1400_, lean_object* v_n_1401_, lean_object* v_as_1402_, lean_object* v_lo_1403_, lean_object* v_hi_1404_){
_start:
{
lean_object* v___y_1406_; uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_lt(v_lo_1403_, v_hi_1404_);
if (v___x_1416_ == 0)
{
lean_dec(v_lo_1403_);
return v_as_1402_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v_mid_1419_; lean_object* v___y_1421_; lean_object* v___y_1427_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1417_ = lean_nat_add(v_lo_1403_, v_hi_1404_);
v___x_1418_ = lean_unsigned_to_nat(1u);
v_mid_1419_ = lean_nat_shiftr(v___x_1417_, v___x_1418_);
lean_dec(v___x_1417_);
v___x_1432_ = lean_array_fget_borrowed(v_as_1402_, v_mid_1419_);
v___x_1433_ = lean_array_fget_borrowed(v_as_1402_, v_lo_1403_);
lean_inc(v___x_1433_);
lean_inc(v___x_1432_);
v___x_1434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1400_, v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
v___y_1427_ = v_as_1402_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_array_fswap(v_as_1402_, v_lo_1403_, v_mid_1419_);
v___y_1427_ = v___x_1435_;
goto v___jp_1426_;
}
v___jp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1422_ = lean_array_fget_borrowed(v___y_1421_, v_mid_1419_);
v___x_1423_ = lean_array_fget_borrowed(v___y_1421_, v_hi_1404_);
lean_inc(v___x_1423_);
lean_inc(v___x_1422_);
v___x_1424_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1400_, v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec(v_mid_1419_);
v___y_1406_ = v___y_1421_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_array_fswap(v___y_1421_, v_mid_1419_, v_hi_1404_);
lean_dec(v_mid_1419_);
v___y_1406_ = v___x_1425_;
goto v___jp_1405_;
}
}
v___jp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_array_fget_borrowed(v___y_1427_, v_hi_1404_);
v___x_1429_ = lean_array_fget_borrowed(v___y_1427_, v_lo_1403_);
lean_inc(v___x_1429_);
lean_inc(v___x_1428_);
v___x_1430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1400_, v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
v___y_1421_ = v___y_1427_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_array_fswap(v___y_1427_, v_lo_1403_, v_hi_1404_);
v___y_1421_ = v___x_1431_;
goto v___jp_1420_;
}
}
}
v___jp_1405_:
{
lean_object* v_pivot_1407_; lean_object* v___x_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; uint8_t v___x_1411_; 
v_pivot_1407_ = lean_array_fget(v___y_1406_, v_hi_1404_);
lean_inc_n(v_lo_1403_, 2);
v___x_1408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1400_, v_hi_1404_, v_pivot_1407_, v___y_1406_, v_lo_1403_, v_lo_1403_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_fst_1409_);
v_snd_1410_ = lean_ctor_get(v___x_1408_, 1);
lean_inc(v_snd_1410_);
lean_dec_ref(v___x_1408_);
v___x_1411_ = lean_nat_dec_le(v_hi_1404_, v_fst_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1400_, v_n_1401_, v_snd_1410_, v_lo_1403_, v_fst_1409_);
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_nat_add(v_fst_1409_, v___x_1413_);
lean_dec(v_fst_1409_);
v_as_1402_ = v___x_1412_;
v_lo_1403_ = v___x_1414_;
goto _start;
}
else
{
lean_dec(v_fst_1409_);
lean_dec(v_lo_1403_);
return v_snd_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_1436_, lean_object* v_n_1437_, lean_object* v_as_1438_, lean_object* v_lo_1439_, lean_object* v_hi_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1436_, v_n_1437_, v_as_1438_, v_lo_1439_, v_hi_1440_);
lean_dec(v_hi_1440_);
lean_dec(v_n_1437_);
lean_dec_ref(v___x_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object* v_mvarIds_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; lean_object* v_mctx_1446_; lean_object* v___x_1447_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1445_ = lean_st_ref_get(v___y_1443_);
v_mctx_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc_ref(v_mctx_1446_);
lean_dec(v___x_1445_);
v___x_1447_ = lean_array_get_size(v_mvarIds_1442_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_nat_dec_eq(v___x_1447_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___y_1458_; uint8_t v___x_1460_; 
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_sub(v___x_1447_, v___x_1455_);
v___x_1460_ = lean_nat_dec_le(v___x_1453_, v___x_1456_);
if (v___x_1460_ == 0)
{
lean_inc(v___x_1456_);
v___y_1458_ = v___x_1456_;
goto v___jp_1457_;
}
else
{
v___y_1458_ = v___x_1453_;
goto v___jp_1457_;
}
v___jp_1457_:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_nat_dec_le(v___y_1458_, v___x_1456_);
if (v___x_1459_ == 0)
{
lean_dec(v___x_1456_);
lean_inc(v___y_1458_);
v___y_1449_ = v___y_1458_;
v___y_1450_ = v___y_1458_;
goto v___jp_1448_;
}
else
{
v___y_1449_ = v___y_1458_;
v___y_1450_ = v___x_1456_;
goto v___jp_1448_;
}
}
}
else
{
lean_object* v___x_1461_; 
lean_dec_ref(v_mctx_1446_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_mvarIds_1442_);
return v___x_1461_;
}
v___jp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v_mctx_1446_, v___x_1447_, v_mvarIds_1442_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v_mctx_1446_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object* v_mvarIds_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1462_, v___y_1463_);
lean_dec(v___y_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object* v_k_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v_mctx_1477_; lean_object* v_mvarCounter_1478_; lean_object* v___x_1479_; 
v___x_1476_ = lean_st_ref_get(v___y_1472_);
v_mctx_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_mctx_1477_);
lean_dec(v___x_1476_);
v_mvarCounter_1478_ = lean_ctor_get(v_mctx_1477_, 3);
lean_inc(v_mvarCounter_1478_);
lean_dec_ref(v_mctx_1477_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
v___x_1479_ = lean_apply_9(v_k_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, lean_box(0));
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_n(v_a_1480_, 2);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = l_Lean_Meta_getMVarsNoDelayed(v_a_1480_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1482_, v_mvarCounter_1478_, v___y_1472_);
lean_dec(v_mvarCounter_1478_);
lean_dec(v_a_1482_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_a_1484_, v___y_1472_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1480_);
lean_ctor_set(v___x_1490_, 1, v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_a_1480_);
lean_dec(v_mvarCounter_1478_);
v_a_1495_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1481_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1481_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_mvarCounter_1478_);
v_a_1503_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1479_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1479_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object* v_k_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* v_k_1522_, lean_object* v_parentTag_1523_, lean_object* v_tagSuffix_1524_, uint8_t v_allowNaturalHoles_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1522_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_fst_1537_; lean_object* v_snd_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1618_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v_fst_1537_ = lean_ctor_get(v_a_1536_, 0);
v_snd_1538_ = lean_ctor_get(v_a_1536_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_a_1536_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1540_ = v_a_1536_;
v_isShared_1541_ = v_isSharedCheck_1618_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_snd_1538_);
lean_inc(v_fst_1537_);
lean_dec(v_a_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1618_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1574_; lean_object* v_a_1575_; lean_object* v___x_1585_; lean_object* v_a_1587_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1603_ = lean_array_get_size(v_snd_1538_);
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1605_ = lean_nat_dec_lt(v___x_1585_, v___x_1603_);
if (v___x_1605_ == 0)
{
lean_dec(v_snd_1538_);
v_a_1587_ = v___x_1604_;
goto v___jp_1586_;
}
else
{
size_t v___x_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = lean_usize_of_nat(v___x_1603_);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1538_, v___x_1606_, v___x_1607_, v___x_1604_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_snd_1538_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_a_1587_ = v_a_1609_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1540_);
lean_dec(v_fst_1537_);
lean_dec(v_tagSuffix_1524_);
lean_dec(v_parentTag_1523_);
v_a_1610_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1608_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1608_);
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
v___jp_1542_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_array_to_list(v___y_1543_);
v___x_1553_ = l_Lean_Elab_Tactic_tagUntaggedGoals(v_parentTag_1523_, v_tagSuffix_1524_, v___x_1552_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1563_; 
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1564_);
v___x_1555_ = v___x_1553_;
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1553_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___x_1552_);
v___x_1558_ = v___x_1540_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_fst_1537_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1552_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1558_);
v___x_1560_ = v___x_1555_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
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
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v___x_1552_);
lean_del_object(v___x_1540_);
lean_dec(v_fst_1537_);
v_a_1565_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1553_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1553_);
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
v___jp_1573_:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1575_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec_ref(v_a_1575_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec_ref_known(v___x_1576_, 1);
v___y_1543_ = v___y_1574_;
v___y_1544_ = v_a_1526_;
v___y_1545_ = v_a_1527_;
v___y_1546_ = v_a_1528_;
v___y_1547_ = v_a_1529_;
v___y_1548_ = v_a_1530_;
v___y_1549_ = v_a_1531_;
v___y_1550_ = v_a_1532_;
v___y_1551_ = v_a_1533_;
goto v___jp_1542_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___y_1574_);
lean_del_object(v___x_1540_);
lean_dec(v_fst_1537_);
lean_dec(v_tagSuffix_1524_);
lean_dec(v_parentTag_1523_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v___jp_1586_:
{
if (v_allowNaturalHoles_1525_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1588_ = lean_array_get_size(v_a_1587_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1590_ = lean_nat_dec_lt(v___x_1585_, v___x_1588_);
if (v___x_1590_ == 0)
{
v___y_1574_ = v_a_1587_;
v_a_1575_ = v___x_1589_;
goto v___jp_1573_;
}
else
{
size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = lean_usize_of_nat(v___x_1588_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1587_, v___x_1591_, v___x_1592_, v___x_1589_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1574_ = v_a_1587_;
v_a_1575_ = v_a_1594_;
goto v___jp_1573_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_a_1587_);
lean_del_object(v___x_1540_);
lean_dec(v_fst_1537_);
lean_dec(v_tagSuffix_1524_);
lean_dec(v_parentTag_1523_);
v_a_1595_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1593_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
else
{
v___y_1543_ = v_a_1587_;
v___y_1544_ = v_a_1526_;
v___y_1545_ = v_a_1527_;
v___y_1546_ = v_a_1528_;
v___y_1547_ = v_a_1529_;
v___y_1548_ = v_a_1530_;
v___y_1549_ = v_a_1531_;
v___y_1550_ = v_a_1532_;
v___y_1551_ = v_a_1533_;
goto v___jp_1542_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_tagSuffix_1524_);
lean_dec(v_parentTag_1523_);
v_a_1619_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1535_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1535_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* v_k_1627_, lean_object* v_parentTag_1628_, lean_object* v_tagSuffix_1629_, lean_object* v_allowNaturalHoles_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1640_; lean_object* v_res_1641_; 
v_allowNaturalHoles_boxed_1640_ = lean_unbox(v_allowNaturalHoles_1630_);
v_res_1641_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1627_, v_parentTag_1628_, v_tagSuffix_1629_, v_allowNaturalHoles_boxed_1640_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object* v_as_1642_, size_t v_i_1643_, size_t v_stop_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1642_, v_i_1643_, v_stop_1644_, v_b_1645_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object* v_as_1656_, lean_object* v_i_1657_, lean_object* v_stop_1658_, lean_object* v_b_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
size_t v_i_boxed_1669_; size_t v_stop_boxed_1670_; lean_object* v_res_1671_; 
v_i_boxed_1669_ = lean_unbox_usize(v_i_1657_);
lean_dec(v_i_1657_);
v_stop_boxed_1670_ = lean_unbox_usize(v_stop_1658_);
lean_dec(v_stop_1658_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(v_as_1656_, v_i_boxed_1669_, v_stop_boxed_1670_, v_b_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_as_1656_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object* v_as_1672_, size_t v_i_1673_, size_t v_stop_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1672_, v_i_1673_, v_stop_1674_, v_b_1675_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object* v_as_1686_, lean_object* v_i_1687_, lean_object* v_stop_1688_, lean_object* v_b_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
size_t v_i_boxed_1699_; size_t v_stop_boxed_1700_; lean_object* v_res_1701_; 
v_i_boxed_1699_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_stop_boxed_1700_ = lean_unbox_usize(v_stop_1688_);
lean_dec(v_stop_1688_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(v_as_1686_, v_i_boxed_1699_, v_stop_boxed_1700_, v_b_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v_as_1686_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object* v_mvarIds_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1702_, v___y_1704_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object* v_mvarIds_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(v_mvarIds_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object* v___x_1716_, lean_object* v_n_1717_, lean_object* v_as_1718_, lean_object* v_lo_1719_, lean_object* v_hi_1720_, lean_object* v_w_1721_, lean_object* v_hlo_1722_, lean_object* v_hhi_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1716_, v_n_1717_, v_as_1718_, v_lo_1719_, v_hi_1720_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1725_, lean_object* v_n_1726_, lean_object* v_as_1727_, lean_object* v_lo_1728_, lean_object* v_hi_1729_, lean_object* v_w_1730_, lean_object* v_hlo_1731_, lean_object* v_hhi_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(v___x_1725_, v_n_1726_, v_as_1727_, v_lo_1728_, v_hi_1729_, v_w_1730_, v_hlo_1731_, v_hhi_1732_);
lean_dec(v_hi_1729_);
lean_dec(v_n_1726_);
lean_dec_ref(v___x_1725_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1734_, lean_object* v_n_1735_, lean_object* v_lo_1736_, lean_object* v_hi_1737_, lean_object* v_hhi_1738_, lean_object* v_pivot_1739_, lean_object* v_as_1740_, lean_object* v_i_1741_, lean_object* v_k_1742_, lean_object* v_ilo_1743_, lean_object* v_ik_1744_, lean_object* v_w_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1734_, v_hi_1737_, v_pivot_1739_, v_as_1740_, v_i_1741_, v_k_1742_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1747_, lean_object* v_n_1748_, lean_object* v_lo_1749_, lean_object* v_hi_1750_, lean_object* v_hhi_1751_, lean_object* v_pivot_1752_, lean_object* v_as_1753_, lean_object* v_i_1754_, lean_object* v_k_1755_, lean_object* v_ilo_1756_, lean_object* v_ik_1757_, lean_object* v_w_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(v___x_1747_, v_n_1748_, v_lo_1749_, v_hi_1750_, v_hhi_1751_, v_pivot_1752_, v_as_1753_, v_i_1754_, v_k_1755_, v_ilo_1756_, v_ik_1757_, v_w_1758_);
lean_dec(v_hi_1750_);
lean_dec(v_lo_1749_);
lean_dec(v_n_1748_);
lean_dec_ref(v___x_1747_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object* v_k_1760_, lean_object* v_parentTag_1761_, lean_object* v_tagSuffix_1762_, uint8_t v_allowNaturalHoles_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
if (v_allowNaturalHoles_1763_ == 0)
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1760_, v_parentTag_1761_, v_tagSuffix_1762_, v_allowNaturalHoles_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
return v___x_1773_;
}
else
{
lean_object* v_declName_x3f_1774_; lean_object* v_macroStack_1775_; uint8_t v_mayPostpone_1776_; uint8_t v_errToSorry_1777_; lean_object* v_autoBoundImplicitContext_1778_; lean_object* v_autoBoundImplicitForbidden_1779_; lean_object* v_sectionVars_1780_; lean_object* v_sectionFVars_1781_; uint8_t v_implicitLambda_1782_; uint8_t v_heedElabAsElim_1783_; uint8_t v_isNoncomputableSection_1784_; uint8_t v_isMetaSection_1785_; uint8_t v_ignoreTCFailures_1786_; uint8_t v_inPattern_1787_; lean_object* v_tacSnap_x3f_1788_; uint8_t v_saveRecAppSyntax_1789_; uint8_t v_holesAsSyntheticOpaque_1790_; uint8_t v_checkDeprecated_1791_; lean_object* v_fixedTermElabs_1792_; uint8_t v___y_1794_; 
v_declName_x3f_1774_ = lean_ctor_get(v_a_1766_, 0);
v_macroStack_1775_ = lean_ctor_get(v_a_1766_, 1);
v_mayPostpone_1776_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8);
v_errToSorry_1777_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1778_ = lean_ctor_get(v_a_1766_, 2);
v_autoBoundImplicitForbidden_1779_ = lean_ctor_get(v_a_1766_, 3);
v_sectionVars_1780_ = lean_ctor_get(v_a_1766_, 4);
v_sectionFVars_1781_ = lean_ctor_get(v_a_1766_, 5);
v_implicitLambda_1782_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1783_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1784_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 4);
v_isMetaSection_1785_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1786_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 6);
v_inPattern_1787_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1788_ = lean_ctor_get(v_a_1766_, 6);
v_saveRecAppSyntax_1789_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1790_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 9);
v_checkDeprecated_1791_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1792_ = lean_ctor_get(v_a_1766_, 7);
if (v_holesAsSyntheticOpaque_1790_ == 0)
{
v___y_1794_ = v_allowNaturalHoles_1763_;
goto v___jp_1793_;
}
else
{
v___y_1794_ = v_holesAsSyntheticOpaque_1790_;
goto v___jp_1793_;
}
v___jp_1793_:
{
lean_object* v___x_1795_; uint8_t v_foApprox_1796_; uint8_t v_ctxApprox_1797_; uint8_t v_quasiPatternApprox_1798_; uint8_t v_constApprox_1799_; uint8_t v_isDefEqStuckEx_1800_; uint8_t v_unificationHints_1801_; uint8_t v_proofIrrelevance_1802_; uint8_t v_offsetCnstrs_1803_; uint8_t v_transparency_1804_; uint8_t v_etaStruct_1805_; uint8_t v_univApprox_1806_; uint8_t v_iota_1807_; uint8_t v_beta_1808_; uint8_t v_proj_1809_; uint8_t v_zeta_1810_; uint8_t v_zetaDelta_1811_; uint8_t v_zetaUnused_1812_; uint8_t v_zetaHave_1813_; uint8_t v_canUnfoldPredicateConfig_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1844_; 
v___x_1795_ = l_Lean_Meta_Context_config(v_a_1768_);
v_foApprox_1796_ = lean_ctor_get_uint8(v___x_1795_, 0);
v_ctxApprox_1797_ = lean_ctor_get_uint8(v___x_1795_, 1);
v_quasiPatternApprox_1798_ = lean_ctor_get_uint8(v___x_1795_, 2);
v_constApprox_1799_ = lean_ctor_get_uint8(v___x_1795_, 3);
v_isDefEqStuckEx_1800_ = lean_ctor_get_uint8(v___x_1795_, 4);
v_unificationHints_1801_ = lean_ctor_get_uint8(v___x_1795_, 5);
v_proofIrrelevance_1802_ = lean_ctor_get_uint8(v___x_1795_, 6);
v_offsetCnstrs_1803_ = lean_ctor_get_uint8(v___x_1795_, 8);
v_transparency_1804_ = lean_ctor_get_uint8(v___x_1795_, 9);
v_etaStruct_1805_ = lean_ctor_get_uint8(v___x_1795_, 10);
v_univApprox_1806_ = lean_ctor_get_uint8(v___x_1795_, 11);
v_iota_1807_ = lean_ctor_get_uint8(v___x_1795_, 12);
v_beta_1808_ = lean_ctor_get_uint8(v___x_1795_, 13);
v_proj_1809_ = lean_ctor_get_uint8(v___x_1795_, 14);
v_zeta_1810_ = lean_ctor_get_uint8(v___x_1795_, 15);
v_zetaDelta_1811_ = lean_ctor_get_uint8(v___x_1795_, 16);
v_zetaUnused_1812_ = lean_ctor_get_uint8(v___x_1795_, 17);
v_zetaHave_1813_ = lean_ctor_get_uint8(v___x_1795_, 18);
v_canUnfoldPredicateConfig_1814_ = lean_ctor_get_uint8(v___x_1795_, 19);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1816_ = v___x_1795_;
v_isShared_1817_ = v_isSharedCheck_1844_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v___x_1795_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1844_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
uint8_t v_trackZetaDelta_1818_; lean_object* v_zetaDeltaSet_1819_; lean_object* v_lctx_1820_; lean_object* v_localInstances_1821_; lean_object* v_defEqCtx_x3f_1822_; lean_object* v_synthPendingDepth_1823_; lean_object* v_customCanUnfoldPredicate_x3f_1824_; uint8_t v_univApprox_1825_; uint8_t v_inTypeClassResolution_1826_; uint8_t v_cacheInferType_1827_; lean_object* v___x_1829_; 
v_trackZetaDelta_1818_ = lean_ctor_get_uint8(v_a_1768_, sizeof(void*)*7);
v_zetaDeltaSet_1819_ = lean_ctor_get(v_a_1768_, 1);
v_lctx_1820_ = lean_ctor_get(v_a_1768_, 2);
v_localInstances_1821_ = lean_ctor_get(v_a_1768_, 3);
v_defEqCtx_x3f_1822_ = lean_ctor_get(v_a_1768_, 4);
v_synthPendingDepth_1823_ = lean_ctor_get(v_a_1768_, 5);
v_customCanUnfoldPredicate_x3f_1824_ = lean_ctor_get(v_a_1768_, 6);
v_univApprox_1825_ = lean_ctor_get_uint8(v_a_1768_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1826_ = lean_ctor_get_uint8(v_a_1768_, sizeof(void*)*7 + 2);
v_cacheInferType_1827_ = lean_ctor_get_uint8(v_a_1768_, sizeof(void*)*7 + 3);
if (v_isShared_1817_ == 0)
{
v___x_1829_ = v___x_1816_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 0, v_foApprox_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 1, v_ctxApprox_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 2, v_quasiPatternApprox_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 3, v_constApprox_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 4, v_isDefEqStuckEx_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 5, v_unificationHints_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 6, v_proofIrrelevance_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 8, v_offsetCnstrs_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 9, v_transparency_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 10, v_etaStruct_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 11, v_univApprox_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 12, v_iota_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 13, v_beta_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 14, v_proj_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 15, v_zeta_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 16, v_zetaDelta_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 17, v_zetaUnused_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 18, v_zetaHave_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, 19, v_canUnfoldPredicateConfig_1814_);
v___x_1829_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
uint64_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_ctor_set_uint8(v___x_1829_, 7, v_allowNaturalHoles_1763_);
v___x_1830_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1829_);
lean_inc_ref(v_fixedTermElabs_1792_);
lean_inc(v_tacSnap_x3f_1788_);
lean_inc(v_sectionFVars_1781_);
lean_inc(v_sectionVars_1780_);
lean_inc_ref(v_autoBoundImplicitForbidden_1779_);
lean_inc(v_autoBoundImplicitContext_1778_);
lean_inc(v_macroStack_1775_);
lean_inc(v_declName_x3f_1774_);
v___x_1831_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1831_, 0, v_declName_x3f_1774_);
lean_ctor_set(v___x_1831_, 1, v_macroStack_1775_);
lean_ctor_set(v___x_1831_, 2, v_autoBoundImplicitContext_1778_);
lean_ctor_set(v___x_1831_, 3, v_autoBoundImplicitForbidden_1779_);
lean_ctor_set(v___x_1831_, 4, v_sectionVars_1780_);
lean_ctor_set(v___x_1831_, 5, v_sectionFVars_1781_);
lean_ctor_set(v___x_1831_, 6, v_tacSnap_x3f_1788_);
lean_ctor_set(v___x_1831_, 7, v_fixedTermElabs_1792_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8, v_mayPostpone_1776_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 1, v_errToSorry_1777_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 2, v_implicitLambda_1782_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 3, v_heedElabAsElim_1783_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1784_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 5, v_isMetaSection_1785_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1786_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 7, v_inPattern_1787_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1789_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 9, v___y_1794_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*8 + 10, v_checkDeprecated_1791_);
v___x_1832_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
lean_ctor_set_uint64(v___x_1832_, sizeof(void*)*1, v___x_1830_);
lean_inc(v_customCanUnfoldPredicate_x3f_1824_);
lean_inc(v_synthPendingDepth_1823_);
lean_inc(v_defEqCtx_x3f_1822_);
lean_inc_ref(v_localInstances_1821_);
lean_inc_ref(v_lctx_1820_);
lean_inc(v_zetaDeltaSet_1819_);
v___x_1833_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_zetaDeltaSet_1819_);
lean_ctor_set(v___x_1833_, 2, v_lctx_1820_);
lean_ctor_set(v___x_1833_, 3, v_localInstances_1821_);
lean_ctor_set(v___x_1833_, 4, v_defEqCtx_x3f_1822_);
lean_ctor_set(v___x_1833_, 5, v_synthPendingDepth_1823_);
lean_ctor_set(v___x_1833_, 6, v_customCanUnfoldPredicate_x3f_1824_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*7, v_trackZetaDelta_1818_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*7 + 1, v_univApprox_1825_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1826_);
lean_ctor_set_uint8(v___x_1833_, sizeof(void*)*7 + 3, v_cacheInferType_1827_);
v___x_1834_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1760_, v_parentTag_1761_, v_tagSuffix_1762_, v_allowNaturalHoles_1763_, v_a_1764_, v_a_1765_, v___x_1831_, v_a_1767_, v___x_1833_, v_a_1769_, v_a_1770_, v_a_1771_);
lean_dec_ref_known(v___x_1833_, 7);
lean_dec_ref_known(v___x_1831_, 8);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
return v___x_1834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object* v_k_1845_, lean_object* v_parentTag_1846_, lean_object* v_tagSuffix_1847_, lean_object* v_allowNaturalHoles_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1858_; lean_object* v_res_1859_; 
v_allowNaturalHoles_boxed_1858_ = lean_unbox(v_allowNaturalHoles_1848_);
v_res_1859_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v_k_1845_, v_parentTag_1846_, v_tagSuffix_1847_, v_allowNaturalHoles_boxed_1858_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* v_stx_1860_, lean_object* v_expectedType_x3f_1861_, lean_object* v_tagSuffix_1862_, uint8_t v_allowNaturalHoles_1863_, lean_object* v_parentTag_x3f_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_a_1875_; 
if (lean_obj_tag(v_parentTag_x3f_1864_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Elab_Tactic_getMainTag___redArg(v_a_1866_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_a_1875_ = v_a_1881_;
goto v___jp_1874_;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_tagSuffix_1862_);
lean_dec(v_expectedType_x3f_1861_);
lean_dec(v_stx_1860_);
v_a_1882_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1880_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1880_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_val_1890_; 
v_val_1890_ = lean_ctor_get(v_parentTag_x3f_1864_, 0);
lean_inc(v_val_1890_);
lean_dec_ref_known(v_parentTag_x3f_1864_, 1);
v_a_1875_ = v_val_1890_;
goto v___jp_1874_;
}
v___jp_1874_:
{
uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = 0;
v___x_1877_ = lean_box(v___x_1876_);
v___x_1878_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(v___x_1878_, 0, v_stx_1860_);
lean_closure_set(v___x_1878_, 1, v_expectedType_x3f_1861_);
lean_closure_set(v___x_1878_, 2, v___x_1877_);
v___x_1879_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_1878_, v_a_1875_, v_tagSuffix_1862_, v_allowNaturalHoles_1863_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* v_stx_1891_, lean_object* v_expectedType_x3f_1892_, lean_object* v_tagSuffix_1893_, lean_object* v_allowNaturalHoles_1894_, lean_object* v_parentTag_x3f_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1905_; lean_object* v_res_1906_; 
v_allowNaturalHoles_boxed_1905_ = lean_unbox(v_allowNaturalHoles_1894_);
v_res_1906_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_1891_, v_expectedType_x3f_1892_, v_tagSuffix_1893_, v_allowNaturalHoles_boxed_1905_, v_parentTag_x3f_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
return v_res_1906_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object* v_a_1907_, lean_object* v_x_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_instBEqMVarId_beq(v_x_1908_, v_a_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object* v_a_1910_, lean_object* v_x_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Lean_Elab_Tactic_refineCore___lam__0(v_a_1910_, v_x_1911_);
lean_dec(v_x_1911_);
lean_dec(v_a_1910_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v_ks_1918_; lean_object* v_vs_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1943_; 
v_ks_1918_ = lean_ctor_get(v_x_1914_, 0);
v_vs_1919_ = lean_ctor_get(v_x_1914_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_x_1914_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1921_ = v_x_1914_;
v_isShared_1922_ = v_isSharedCheck_1943_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_vs_1919_);
lean_inc(v_ks_1918_);
lean_dec(v_x_1914_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1943_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = lean_array_get_size(v_ks_1918_);
v___x_1924_ = lean_nat_dec_lt(v_x_1915_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_dec(v_x_1915_);
v___x_1925_ = lean_array_push(v_ks_1918_, v_x_1916_);
v___x_1926_ = lean_array_push(v_vs_1919_, v_x_1917_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v___x_1926_);
lean_ctor_set(v___x_1921_, 0, v___x_1925_);
v___x_1928_ = v___x_1921_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
else
{
lean_object* v_k_x27_1930_; uint8_t v___x_1931_; 
v_k_x27_1930_ = lean_array_fget_borrowed(v_ks_1918_, v_x_1915_);
v___x_1931_ = l_Lean_instBEqMVarId_beq(v_x_1916_, v_k_x27_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1933_; 
if (v_isShared_1922_ == 0)
{
v___x_1933_ = v___x_1921_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_ks_1918_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_vs_1919_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_add(v_x_1915_, v___x_1934_);
lean_dec(v_x_1915_);
v_x_1914_ = v___x_1933_;
v_x_1915_ = v___x_1935_;
goto _start;
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1938_ = lean_array_fset(v_ks_1918_, v_x_1915_, v_x_1916_);
v___x_1939_ = lean_array_fset(v_vs_1919_, v_x_1915_, v_x_1917_);
lean_dec(v_x_1915_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v___x_1939_);
lean_ctor_set(v___x_1921_, 0, v___x_1938_);
v___x_1941_ = v___x_1921_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___x_1939_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_1944_, lean_object* v_k_1945_, lean_object* v_v_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_1944_, v___x_1947_, v_k_1945_, v_v_1946_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1950_, size_t v_x_1951_, size_t v_x_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 0)
{
lean_object* v_es_1955_; size_t v___x_1956_; size_t v___x_1957_; lean_object* v_j_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_es_1955_ = lean_ctor_get(v_x_1950_, 0);
v___x_1956_ = ((size_t)31ULL);
v___x_1957_ = lean_usize_land(v_x_1951_, v___x_1956_);
v_j_1958_ = lean_usize_to_nat(v___x_1957_);
v___x_1959_ = lean_array_get_size(v_es_1955_);
v___x_1960_ = lean_nat_dec_lt(v_j_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_dec(v_j_1958_);
lean_dec(v_x_1954_);
lean_dec(v_x_1953_);
return v_x_1950_;
}
else
{
lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1999_; 
lean_inc_ref(v_es_1955_);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v_x_1950_, 0);
lean_dec(v_unused_2000_);
v___x_1962_ = v_x_1950_;
v_isShared_1963_ = v_isSharedCheck_1999_;
goto v_resetjp_1961_;
}
else
{
lean_dec(v_x_1950_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1999_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_v_1964_; lean_object* v___x_1965_; lean_object* v_xs_x27_1966_; lean_object* v___y_1968_; 
v_v_1964_ = lean_array_fget(v_es_1955_, v_j_1958_);
v___x_1965_ = lean_box(0);
v_xs_x27_1966_ = lean_array_fset(v_es_1955_, v_j_1958_, v___x_1965_);
switch(lean_obj_tag(v_v_1964_))
{
case 0:
{
lean_object* v_key_1973_; lean_object* v_val_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1984_; 
v_key_1973_ = lean_ctor_get(v_v_1964_, 0);
v_val_1974_ = lean_ctor_get(v_v_1964_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_v_1964_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1976_ = v_v_1964_;
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_val_1974_);
lean_inc(v_key_1973_);
lean_dec(v_v_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_instBEqMVarId_beq(v_x_1953_, v_key_1973_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_del_object(v___x_1976_);
v___x_1979_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1973_, v_val_1974_, v_x_1953_, v_x_1954_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___y_1968_ = v___x_1980_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_val_1974_);
lean_dec(v_key_1973_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_x_1954_);
lean_ctor_set(v___x_1976_, 0, v_x_1953_);
v___x_1982_ = v___x_1976_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_x_1953_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_x_1954_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
v___y_1968_ = v___x_1982_;
goto v___jp_1967_;
}
}
}
}
case 1:
{
lean_object* v_node_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
v_node_1985_ = lean_ctor_get(v_v_1964_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_v_1964_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1987_ = v_v_1964_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_node_1985_);
lean_dec(v_v_1964_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
size_t v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1989_ = ((size_t)5ULL);
v___x_1990_ = lean_usize_shift_right(v_x_1951_, v___x_1989_);
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_add(v_x_1952_, v___x_1991_);
v___x_1993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_node_1985_, v___x_1990_, v___x_1992_, v_x_1953_, v_x_1954_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1993_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
v___y_1968_ = v___x_1995_;
goto v___jp_1967_;
}
}
}
default: 
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_x_1953_);
lean_ctor_set(v___x_1998_, 1, v_x_1954_);
v___y_1968_ = v___x_1998_;
goto v___jp_1967_;
}
}
v___jp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_array_fset(v_xs_x27_1966_, v_j_1958_, v___y_1968_);
lean_dec(v_j_1958_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1969_);
v___x_1971_ = v___x_1962_;
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
}
}
else
{
lean_object* v_ks_2001_; lean_object* v_vs_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2020_; 
v_ks_2001_ = lean_ctor_get(v_x_1950_, 0);
v_vs_2002_ = lean_ctor_get(v_x_1950_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2004_ = v_x_1950_;
v_isShared_2005_ = v_isSharedCheck_2020_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_vs_2002_);
lean_inc(v_ks_2001_);
lean_dec(v_x_1950_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2020_;
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
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_ks_2001_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_vs_2002_);
v___x_2007_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v_newNode_2008_; size_t v___x_2009_; uint8_t v___x_2010_; 
v_newNode_2008_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_2007_, v_x_1953_, v_x_1954_);
v___x_2009_ = ((size_t)7ULL);
v___x_2010_ = lean_usize_dec_le(v___x_2009_, v_x_1952_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2008_);
v___x_2012_ = lean_unsigned_to_nat(4u);
v___x_2013_ = lean_nat_dec_lt(v___x_2011_, v___x_2012_);
lean_dec(v___x_2011_);
if (v___x_2013_ == 0)
{
lean_object* v_ks_2014_; lean_object* v_vs_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_ks_2014_ = lean_ctor_get(v_newNode_2008_, 0);
lean_inc_ref(v_ks_2014_);
v_vs_2015_ = lean_ctor_get(v_newNode_2008_, 1);
lean_inc_ref(v_vs_2015_);
lean_dec_ref(v_newNode_2008_);
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2018_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1952_, v_ks_2014_, v_vs_2015_, v___x_2016_, v___x_2017_);
lean_dec_ref(v_vs_2015_);
lean_dec_ref(v_ks_2014_);
return v___x_2018_;
}
else
{
return v_newNode_2008_;
}
}
else
{
return v_newNode_2008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_2021_, lean_object* v_keys_2022_, lean_object* v_vals_2023_, lean_object* v_i_2024_, lean_object* v_entries_2025_){
_start:
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = lean_array_get_size(v_keys_2022_);
v___x_2027_ = lean_nat_dec_lt(v_i_2024_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_i_2024_);
return v_entries_2025_;
}
else
{
lean_object* v_k_2028_; lean_object* v_v_2029_; uint64_t v___x_2030_; size_t v_h_2031_; size_t v___x_2032_; lean_object* v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; size_t v_h_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_k_2028_ = lean_array_fget_borrowed(v_keys_2022_, v_i_2024_);
v_v_2029_ = lean_array_fget_borrowed(v_vals_2023_, v_i_2024_);
v___x_2030_ = l_Lean_instHashableMVarId_hash(v_k_2028_);
v_h_2031_ = lean_uint64_to_usize(v___x_2030_);
v___x_2032_ = ((size_t)5ULL);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_sub(v_depth_2021_, v___x_2034_);
v___x_2036_ = lean_usize_mul(v___x_2032_, v___x_2035_);
v_h_2037_ = lean_usize_shift_right(v_h_2031_, v___x_2036_);
v___x_2038_ = lean_nat_add(v_i_2024_, v___x_2033_);
lean_dec(v_i_2024_);
lean_inc(v_v_2029_);
lean_inc(v_k_2028_);
v___x_2039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_entries_2025_, v_h_2037_, v_depth_2021_, v_k_2028_, v_v_2029_);
v_i_2024_ = v___x_2038_;
v_entries_2025_ = v___x_2039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_2041_, lean_object* v_keys_2042_, lean_object* v_vals_2043_, lean_object* v_i_2044_, lean_object* v_entries_2045_){
_start:
{
size_t v_depth_boxed_2046_; lean_object* v_res_2047_; 
v_depth_boxed_2046_ = lean_unbox_usize(v_depth_2041_);
lean_dec(v_depth_2041_);
v_res_2047_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_2046_, v_keys_2042_, v_vals_2043_, v_i_2044_, v_entries_2045_);
lean_dec_ref(v_vals_2043_);
lean_dec_ref(v_keys_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
size_t v_x_3361__boxed_2053_; size_t v_x_3362__boxed_2054_; lean_object* v_res_2055_; 
v_x_3361__boxed_2053_ = lean_unbox_usize(v_x_2049_);
lean_dec(v_x_2049_);
v_x_3362__boxed_2054_ = lean_unbox_usize(v_x_2050_);
lean_dec(v_x_2050_);
v_res_2055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2048_, v_x_3361__boxed_2053_, v_x_3362__boxed_2054_, v_x_2051_, v_x_2052_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
uint64_t v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = l_Lean_instHashableMVarId_hash(v_x_2057_);
v___x_2060_ = lean_uint64_to_usize(v___x_2059_);
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2056_, v___x_2060_, v___x_2061_, v_x_2057_, v_x_2058_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object* v_mvarId_2063_, lean_object* v_val_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v_mctx_2068_; lean_object* v_cache_2069_; lean_object* v_zetaDeltaFVarIds_2070_; lean_object* v_postponed_2071_; lean_object* v_diag_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2102_; 
v___x_2067_ = lean_st_ref_take(v___y_2065_);
v_mctx_2068_ = lean_ctor_get(v___x_2067_, 0);
v_cache_2069_ = lean_ctor_get(v___x_2067_, 1);
v_zetaDeltaFVarIds_2070_ = lean_ctor_get(v___x_2067_, 2);
v_postponed_2071_ = lean_ctor_get(v___x_2067_, 3);
v_diag_2072_ = lean_ctor_get(v___x_2067_, 4);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2074_ = v___x_2067_;
v_isShared_2075_ = v_isSharedCheck_2102_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_diag_2072_);
lean_inc(v_postponed_2071_);
lean_inc(v_zetaDeltaFVarIds_2070_);
lean_inc(v_cache_2069_);
lean_inc(v_mctx_2068_);
lean_dec(v___x_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2102_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_depth_2076_; lean_object* v_levelAssignDepth_2077_; lean_object* v_lmvarCounter_2078_; lean_object* v_mvarCounter_2079_; lean_object* v_lDecls_2080_; lean_object* v_decls_2081_; lean_object* v_userNames_2082_; lean_object* v_lAssignment_2083_; lean_object* v_eAssignment_2084_; lean_object* v_dAssignment_2085_; lean_object* v_instanceTypedMVars_2086_; lean_object* v_synthNormMemo_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2101_; 
v_depth_2076_ = lean_ctor_get(v_mctx_2068_, 0);
v_levelAssignDepth_2077_ = lean_ctor_get(v_mctx_2068_, 1);
v_lmvarCounter_2078_ = lean_ctor_get(v_mctx_2068_, 2);
v_mvarCounter_2079_ = lean_ctor_get(v_mctx_2068_, 3);
v_lDecls_2080_ = lean_ctor_get(v_mctx_2068_, 4);
v_decls_2081_ = lean_ctor_get(v_mctx_2068_, 5);
v_userNames_2082_ = lean_ctor_get(v_mctx_2068_, 6);
v_lAssignment_2083_ = lean_ctor_get(v_mctx_2068_, 7);
v_eAssignment_2084_ = lean_ctor_get(v_mctx_2068_, 8);
v_dAssignment_2085_ = lean_ctor_get(v_mctx_2068_, 9);
v_instanceTypedMVars_2086_ = lean_ctor_get(v_mctx_2068_, 10);
v_synthNormMemo_2087_ = lean_ctor_get(v_mctx_2068_, 11);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_mctx_2068_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2089_ = v_mctx_2068_;
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_synthNormMemo_2087_);
lean_inc(v_instanceTypedMVars_2086_);
lean_inc(v_dAssignment_2085_);
lean_inc(v_eAssignment_2084_);
lean_inc(v_lAssignment_2083_);
lean_inc(v_userNames_2082_);
lean_inc(v_decls_2081_);
lean_inc(v_lDecls_2080_);
lean_inc(v_mvarCounter_2079_);
lean_inc(v_lmvarCounter_2078_);
lean_inc(v_levelAssignDepth_2077_);
lean_inc(v_depth_2076_);
lean_dec(v_mctx_2068_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_eAssignment_2084_, v_mvarId_2063_, v_val_2064_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 8, v___x_2092_);
v___x_2094_ = v___x_2089_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_depth_2076_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_levelAssignDepth_2077_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_lmvarCounter_2078_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_mvarCounter_2079_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_lDecls_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 5, v_decls_2081_);
lean_ctor_set(v_reuseFailAlloc_2100_, 6, v_userNames_2082_);
lean_ctor_set(v_reuseFailAlloc_2100_, 7, v_lAssignment_2083_);
lean_ctor_set(v_reuseFailAlloc_2100_, 8, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2100_, 9, v_dAssignment_2085_);
lean_ctor_set(v_reuseFailAlloc_2100_, 10, v_instanceTypedMVars_2086_);
lean_ctor_set(v_reuseFailAlloc_2100_, 11, v_synthNormMemo_2087_);
v___x_2094_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2094_);
v___x_2096_ = v___x_2074_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_cache_2069_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_zetaDeltaFVarIds_2070_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_postponed_2071_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v_diag_2072_);
v___x_2096_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_st_ref_put(v___y_2065_, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2091_);
return v___x_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object* v_mvarId_2103_, lean_object* v_val_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2103_, v_val_2104_, v___y_2105_);
lean_dec(v___y_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(lean_object* v_msgData_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v_env_2115_; uint8_t v___x_2116_; lean_object* v_env_2117_; lean_object* v___x_2118_; lean_object* v_toCold_2119_; lean_object* v_mctx_2120_; lean_object* v_lctx_2121_; lean_object* v_options_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2114_ = lean_st_ref_get(v___y_2112_);
v_env_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_ref(v_env_2115_);
lean_dec(v___x_2114_);
v___x_2116_ = 0;
v_env_2117_ = l_Lean_Environment_setRecordingDeps(v_env_2115_, v___x_2116_);
v___x_2118_ = lean_st_ref_get(v___y_2110_);
v_toCold_2119_ = lean_ctor_get(v___y_2111_, 0);
v_mctx_2120_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_ref(v_mctx_2120_);
lean_dec(v___x_2118_);
v_lctx_2121_ = lean_ctor_get(v___y_2109_, 2);
v_options_2122_ = lean_ctor_get(v_toCold_2119_, 2);
lean_inc_ref(v_options_2122_);
lean_inc_ref(v_lctx_2121_);
v___x_2123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2123_, 0, v_env_2117_);
lean_ctor_set(v___x_2123_, 1, v_mctx_2120_);
lean_ctor_set(v___x_2123_, 2, v_lctx_2121_);
lean_ctor_set(v___x_2123_, 3, v_options_2122_);
v___x_2124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v_msgData_2108_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(lean_object* v_msgData_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msgData_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(lean_object* v_msg_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_ref_2139_; lean_object* v___x_2140_; lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2149_; 
v_ref_2139_ = lean_ctor_get(v___y_2136_, 2);
v___x_2140_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2149_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2149_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
lean_inc(v_ref_2139_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_ref_2139_);
lean_ctor_set(v___x_2145_, 1, v_a_2141_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 1);
lean_ctor_set(v___x_2143_, 0, v___x_2145_);
v___x_2147_ = v___x_2143_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2156_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__0));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__2));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__4));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object* v_stx_2166_, lean_object* v_tagSuffix_2167_, uint8_t v_allowNaturalHoles_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Elab_Tactic_getMainTarget(v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2179_);
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_2166_, v___x_2180_, v_tagSuffix_2167_, v_allowNaturalHoles_2168_, v___x_2181_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2232_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v_fst_2184_ = lean_ctor_get(v_a_2183_, 0);
v_snd_2185_ = lean_ctor_get(v_a_2183_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2187_ = v_a_2183_;
v_isShared_2188_ = v_isSharedCheck_2232_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_snd_2185_);
lean_inc(v_fst_2184_);
lean_dec(v_a_2183_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2232_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2170_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v_a_2193_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc_n(v_a_2190_, 3);
lean_dec_ref_known(v___x_2189_, 1);
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2191_, 0, v_a_2190_);
v___x_2192_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_fst_2184_, v___y_2174_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
v___x_2205_ = l_Lean_mkMVar(v_a_2190_);
v___x_2206_ = lean_expr_eqv(v_a_2193_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
lean_inc(v_a_2193_);
v___x_2207_ = l_Lean_FindMVar_main(v___f_2191_, v_a_2193_, v___x_2181_);
if (lean_obj_tag(v___x_2207_) == 1)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_dec_ref_known(v___x_2207_, 1);
lean_dec(v_a_2190_);
lean_dec(v_snd_2185_);
v___x_2208_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__1, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1);
v___x_2209_ = l_Lean_indentExpr(v_a_2193_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set_tag(v___x_2187_, 7);
lean_ctor_set(v___x_2187_, 1, v___x_2209_);
lean_ctor_set(v___x_2187_, 0, v___x_2208_);
v___x_2211_ = v___x_2187_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2212_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__3, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = l_Lean_MessageData_ofExpr(v___x_2205_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_2217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2217_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2218_;
}
}
else
{
lean_dec(v___x_2207_);
lean_dec_ref(v___x_2205_);
lean_del_object(v___x_2187_);
v___y_2195_ = v___y_2169_;
v___y_2196_ = v___y_2170_;
v___y_2197_ = v___y_2171_;
v___y_2198_ = v___y_2172_;
v___y_2199_ = v___y_2173_;
v___y_2200_ = v___y_2174_;
v___y_2201_ = v___y_2175_;
v___y_2202_ = v___y_2176_;
goto v___jp_2194_;
}
}
else
{
lean_object* v___x_2221_; 
lean_dec_ref(v___x_2205_);
lean_dec(v_a_2193_);
lean_dec_ref(v___f_2191_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set_tag(v___x_2187_, 1);
lean_ctor_set(v___x_2187_, 0, v_a_2190_);
v___x_2221_ = v___x_2187_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2190_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_snd_2185_);
v___x_2221_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2221_, v___y_2170_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2222_;
}
}
v___jp_2194_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_a_2190_, v_a_2193_, v___y_2200_);
lean_dec_ref(v___x_2203_);
v___x_2204_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_2185_, v___y_2196_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_del_object(v___x_2187_);
lean_dec(v_snd_2185_);
lean_dec(v_fst_2184_);
v_a_2224_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2189_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2189_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2182_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2182_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_tagSuffix_2167_);
lean_dec(v_stx_2166_);
v_a_2241_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2178_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2178_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object* v_stx_2249_, lean_object* v_tagSuffix_2250_, lean_object* v_allowNaturalHoles_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2261_; lean_object* v_res_2262_; 
v_allowNaturalHoles_boxed_2261_ = lean_unbox(v_allowNaturalHoles_2251_);
v_res_2262_ = l_Lean_Elab_Tactic_refineCore___lam__1(v_stx_2249_, v_tagSuffix_2250_, v_allowNaturalHoles_boxed_2261_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object* v_stx_2263_, lean_object* v_tagSuffix_2264_, uint8_t v_allowNaturalHoles_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_box(v_allowNaturalHoles_2265_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2276_, 0, v_stx_2263_);
lean_closure_set(v___f_2276_, 1, v_tagSuffix_2264_);
lean_closure_set(v___f_2276_, 2, v___x_2275_);
v___x_2277_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2276_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object* v_stx_2278_, lean_object* v_tagSuffix_2279_, lean_object* v_allowNaturalHoles_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2290_; lean_object* v_res_2291_; 
v_allowNaturalHoles_boxed_2290_ = lean_unbox(v_allowNaturalHoles_2280_);
v_res_2291_ = l_Lean_Elab_Tactic_refineCore(v_stx_2278_, v_tagSuffix_2279_, v_allowNaturalHoles_boxed_2290_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(lean_object* v_mvarId_2292_, lean_object* v_val_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2292_, v_val_2293_, v___y_2299_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object* v_mvarId_2304_, lean_object* v_val_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(v_mvarId_2304_, v_val_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(lean_object* v_00_u03b1_2316_, lean_object* v_msg_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2317_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_msg_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(v_00_u03b1_2328_, v_msg_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(lean_object* v_00_u03b2_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_x_2341_, v_x_2342_, v_x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2345_, lean_object* v_x_2346_, size_t v_x_2347_, size_t v_x_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2346_, v_x_2347_, v_x_2348_, v_x_2349_, v_x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
size_t v_x_3911__boxed_2358_; size_t v_x_3912__boxed_2359_; lean_object* v_res_2360_; 
v_x_3911__boxed_2358_ = lean_unbox_usize(v_x_2354_);
lean_dec(v_x_2354_);
v_x_3912__boxed_2359_ = lean_unbox_usize(v_x_2355_);
lean_dec(v_x_2355_);
v_res_2360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(v_00_u03b2_2352_, v_x_2353_, v_x_3911__boxed_2358_, v_x_3912__boxed_2359_, v_x_2356_, v_x_2357_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2361_, lean_object* v_n_2362_, lean_object* v_k_2363_, lean_object* v_v_2364_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_2362_, v_k_2363_, v_v_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2366_, size_t v_depth_2367_, lean_object* v_keys_2368_, lean_object* v_vals_2369_, lean_object* v_heq_2370_, lean_object* v_i_2371_, lean_object* v_entries_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_2367_, v_keys_2368_, v_vals_2369_, v_i_2371_, v_entries_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2374_, lean_object* v_depth_2375_, lean_object* v_keys_2376_, lean_object* v_vals_2377_, lean_object* v_heq_2378_, lean_object* v_i_2379_, lean_object* v_entries_2380_){
_start:
{
size_t v_depth_boxed_2381_; lean_object* v_res_2382_; 
v_depth_boxed_2381_ = lean_unbox_usize(v_depth_2375_);
lean_dec(v_depth_2375_);
v_res_2382_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_2374_, v_depth_boxed_2381_, v_keys_2376_, v_vals_2377_, v_heq_2378_, v_i_2379_, v_entries_2380_);
lean_dec_ref(v_vals_2377_);
lean_dec_ref(v_keys_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_2384_, v_x_2385_, v_x_2386_, v_x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object* v_stx_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
lean_inc(v_stx_2397_);
v___x_2408_ = l_Lean_Syntax_isOfKind(v_stx_2397_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec(v_stx_2397_);
v___x_2409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2409_;
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = l_Lean_Syntax_getArg(v_stx_2397_, v___x_2410_);
lean_dec(v_stx_2397_);
v___x_2412_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__2));
v___x_2413_ = 0;
v___x_2414_ = l_Lean_Elab_Tactic_refineCore(v___x_2411_, v___x_2412_, v___x_2413_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
return v___x_2414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___boxed(lean_object* v_stx_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Elab_Tactic_evalRefine(v_stx_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2433_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
v___x_2435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2436_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine___boxed), 10, 0);
v___x_2437_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2433_, v___x_2434_, v___x_2435_, v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6));
v___x_2468_ = l_Lean_addBuiltinDeclarationRanges(v___x_2466_, v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object* v_stx_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
lean_inc(v_stx_2479_);
v___x_2490_ = l_Lean_Syntax_isOfKind(v_stx_2479_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_stx_2479_);
v___x_2491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = l_Lean_Syntax_getArg(v_stx_2479_, v___x_2492_);
lean_dec(v_stx_2479_);
v___x_2494_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__2));
v___x_2495_ = l_Lean_Elab_Tactic_refineCore(v___x_2493_, v___x_2494_, v___x_2490_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___boxed(lean_object* v_stx_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Elab_Tactic_evalRefine_x27(v_stx_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2514_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2517_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine_x27___boxed), 10, 0);
v___x_2518_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2514_, v___x_2515_, v___x_2516_, v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6));
v___x_2549_ = l_Lean_addBuiltinDeclarationRanges(v___x_2547_, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
return v_res_2551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t v___x_2555_, lean_object* v_stx_2556_, lean_object* v___x_2557_, uint8_t v___x_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
if (v___x_2555_ == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref(v___x_2557_);
v___x_2568_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = l_Lean_Syntax_getArg(v_stx_2556_, v___x_2569_);
v___x_2571_ = lean_box(0);
v___x_2572_ = l_Lean_Name_mkStr1(v___x_2557_);
v___x_2573_ = l_Lean_Elab_Tactic_elabTermWithHoles(v___x_2570_, v___x_2571_, v___x_2572_, v___x_2558_, v___x_2571_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2624_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v_fst_2575_ = lean_ctor_get(v_a_2574_, 0);
v_snd_2576_ = lean_ctor_get(v_a_2574_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_a_2574_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2578_ = v_a_2574_;
v_isShared_2579_ = v_isSharedCheck_2624_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_snd_2576_);
lean_inc(v_fst_2575_);
lean_dec(v_a_2574_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2624_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = l_Lean_Expr_getLambdaBody(v_fst_2575_);
v___x_2581_ = l_Lean_Expr_getAppFn(v___x_2580_);
lean_dec_ref(v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 1)
{
lean_object* v_fvarId_2582_; lean_object* v___x_2583_; 
v_fvarId_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_fvarId_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2560_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
lean_inc(v___y_2566_);
lean_inc_ref(v___y_2565_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
lean_inc(v_fst_2575_);
v___x_2585_ = lean_infer_type(v_fst_2575_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = l_Lean_Expr_headBeta(v_a_2586_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = l_Lean_MVarId_replace(v_a_2584_, v_fvarId_2582_, v_fst_2575_, v___x_2588_, v___x_2571_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v_mvarId_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v_mvarId_2591_ = lean_ctor_get(v_a_2590_, 1);
lean_inc(v_mvarId_2591_);
lean_dec(v_a_2590_);
v___x_2592_ = lean_box(0);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 1);
lean_ctor_set(v___x_2578_, 1, v___x_2592_);
lean_ctor_set(v___x_2578_, 0, v_mvarId_2591_);
v___x_2594_ = v___x_2578_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_mvarId_2591_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = l_List_appendTR___redArg(v_snd_2576_, v___x_2594_);
v___x_2596_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2595_, v___y_2560_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2596_;
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2578_);
lean_dec(v_snd_2576_);
v_a_2598_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2589_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2589_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v_a_2584_);
lean_dec(v_fvarId_2582_);
lean_del_object(v___x_2578_);
lean_dec(v_snd_2576_);
lean_dec(v_fst_2575_);
v_a_2606_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2585_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2585_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_fvarId_2582_);
lean_del_object(v___x_2578_);
lean_dec(v_snd_2576_);
lean_dec(v_fst_2575_);
v_a_2614_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2583_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2583_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec_ref(v___x_2581_);
lean_del_object(v___x_2578_);
lean_dec(v_snd_2576_);
lean_dec(v_fst_2575_);
v___x_2622_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1, &l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1);
v___x_2623_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2622_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2623_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2573_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2573_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object* v___x_2633_, lean_object* v_stx_2634_, lean_object* v___x_2635_, lean_object* v___x_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v___x_958__boxed_2646_; uint8_t v___x_960__boxed_2647_; lean_object* v_res_2648_; 
v___x_958__boxed_2646_ = lean_unbox(v___x_2633_);
v___x_960__boxed_2647_ = lean_unbox(v___x_2636_);
v_res_2648_ = l_Lean_Elab_Tactic_evalSpecialize___lam__0(v___x_958__boxed_2646_, v_stx_2634_, v___x_2635_, v___x_960__boxed_2647_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v_stx_2634_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object* v_stx_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___y_2671_; lean_object* v___x_2672_; 
v___x_2665_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__0));
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
lean_inc(v_stx_2655_);
v___x_2667_ = l_Lean_Syntax_isOfKind(v_stx_2655_, v___x_2666_);
v___x_2668_ = 1;
v___x_2669_ = lean_box(v___x_2667_);
v___x_2670_ = lean_box(v___x_2668_);
v___y_2671_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed), 13, 4);
lean_closure_set(v___y_2671_, 0, v___x_2669_);
lean_closure_set(v___y_2671_, 1, v_stx_2655_);
lean_closure_set(v___y_2671_, 2, v___x_2665_);
lean_closure_set(v___y_2671_, 3, v___x_2670_);
v___x_2672_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_2671_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___boxed(lean_object* v_stx_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Elab_Tactic_evalSpecialize(v_stx_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2691_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2692_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
v___x_2693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___boxed), 10, 0);
v___x_2695_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2691_, v___x_2692_, v___x_2693_, v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6));
v___x_2725_ = l_Lean_addBuiltinDeclarationRanges(v___x_2723_, v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object* v_stx_2729_, uint8_t v_mayPostpone_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; uint8_t v___x_2751_; 
v___x_2751_ = l_Lean_Syntax_isIdent(v_stx_2729_);
if (v___x_2751_ == 0)
{
v___y_2741_ = v_a_2731_;
v___y_2742_ = v_a_2732_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
goto v___jp_2740_;
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_Lean_Elab_Tactic_elabTermForApply___closed__0));
lean_inc(v_stx_2729_);
v___x_2753_ = l_Lean_Elab_Term_resolveId_x3f(v_stx_2729_, v___x_2752_, v___x_2751_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
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
if (lean_obj_tag(v_a_2754_) == 1)
{
lean_object* v_val_2758_; lean_object* v___x_2760_; 
lean_dec(v_stx_2729_);
v_val_2758_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_val_2758_);
lean_dec_ref_known(v_a_2754_, 1);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v_val_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_val_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
else
{
lean_del_object(v___x_2756_);
lean_dec(v_a_2754_);
v___y_2741_ = v_a_2731_;
v___y_2742_ = v_a_2732_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
goto v___jp_2740_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_stx_2729_);
v_a_2763_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2753_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2753_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
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
v___jp_2740_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_box(0);
v___x_2750_ = l_Lean_Elab_Tactic_elabTerm(v_stx_2729_, v___x_2749_, v_mayPostpone_2730_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object* v_stx_2771_, lean_object* v_mayPostpone_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
uint8_t v_mayPostpone_boxed_2782_; lean_object* v_res_2783_; 
v_mayPostpone_boxed_2782_ = lean_unbox(v_mayPostpone_2772_);
v_res_2783_ = l_Lean_Elab_Tactic_elabTermForApply(v_stx_2771_, v_mayPostpone_boxed_2782_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
return v_res_2783_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object* v___x_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2815_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
if (lean_obj_tag(v_a_2801_) == 1)
{
lean_object* v_fvarId_2805_; lean_object* v___x_2807_; 
v_fvarId_2805_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_fvarId_2805_);
lean_dec_ref_known(v_a_2801_, 1);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v_fvarId_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_fvarId_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_del_object(v___x_2803_);
v___x_2809_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1);
v___x_2810_ = l_Lean_MessageData_ofExpr(v_a_2801_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2813_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2800_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2800_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(lean_object* v___x_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Elab_Tactic_getFVarId___lam__0(v___x_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* v_id_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_toCold_2845_; lean_object* v_currRecDepth_2846_; lean_object* v_ref_2847_; uint16_t v_optionFlags_2848_; uint8_t v_suppressElabErrors_2849_; uint8_t v_isRecordingDeps_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v_ref_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_toCold_2845_ = lean_ctor_get(v_a_2842_, 0);
v_currRecDepth_2846_ = lean_ctor_get(v_a_2842_, 1);
v_ref_2847_ = lean_ctor_get(v_a_2842_, 2);
v_optionFlags_2848_ = lean_ctor_get_uint16(v_a_2842_, sizeof(void*)*3);
v_suppressElabErrors_2849_ = lean_ctor_get_uint8(v_a_2842_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2850_ = lean_ctor_get_uint8(v_a_2842_, sizeof(void*)*3 + 3);
v___x_2851_ = 0;
v___x_2852_ = lean_box(v___x_2851_);
lean_inc(v_id_2835_);
v___x_2853_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_2853_, 0, v_id_2835_);
lean_closure_set(v___x_2853_, 1, v___x_2852_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2854_, 0, v___x_2853_);
v_ref_2855_ = l_Lean_replaceRef(v_id_2835_, v_ref_2847_);
lean_dec(v_id_2835_);
lean_inc(v_currRecDepth_2846_);
lean_inc_ref(v_toCold_2845_);
v___x_2856_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2856_, 0, v_toCold_2845_);
lean_ctor_set(v___x_2856_, 1, v_currRecDepth_2846_);
lean_ctor_set(v___x_2856_, 2, v_ref_2855_);
lean_ctor_set_uint16(v___x_2856_, sizeof(void*)*3, v_optionFlags_2848_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*3 + 2, v_suppressElabErrors_2849_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*3 + 3, v_isRecordingDeps_2850_);
v___x_2857_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2854_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v___x_2856_, v_a_2843_);
lean_dec_ref_known(v___x_2856_, 3);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object* v_id_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Elab_Tactic_getFVarId(v_id_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t v_sz_2869_, size_t v_i_2870_, lean_object* v_bs_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_usize_dec_lt(v_i_2870_, v_sz_2869_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_bs_2871_);
return v___x_2882_;
}
else
{
lean_object* v_v_2883_; lean_object* v___x_2884_; lean_object* v_bs_x27_2885_; lean_object* v___x_2886_; 
v_v_2883_ = lean_array_uget(v_bs_2871_, v_i_2870_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v_bs_x27_2885_ = lean_array_uset(v_bs_2871_, v_i_2870_, v___x_2884_);
v___x_2886_ = l_Lean_Elab_Tactic_getFVarId(v_v_2883_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_add(v_i_2870_, v___x_2888_);
v___x_2890_ = lean_array_uset(v_bs_x27_2885_, v_i_2870_, v_a_2887_);
v_i_2870_ = v___x_2889_;
v_bs_2871_ = v___x_2890_;
goto _start;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec_ref(v_bs_x27_2885_);
v_a_2892_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2886_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2886_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object* v_sz_2900_, lean_object* v_i_2901_, lean_object* v_bs_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
size_t v_sz_boxed_2912_; size_t v_i_boxed_2913_; lean_object* v_res_2914_; 
v_sz_boxed_2912_ = lean_unbox_usize(v_sz_2900_);
lean_dec(v_sz_2900_);
v_i_boxed_2913_ = lean_unbox_usize(v_i_2901_);
lean_dec(v_i_2901_);
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(v_sz_boxed_2912_, v_i_boxed_2913_, v_bs_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* v_ids_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
size_t v_sz_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_sz_2927_ = lean_array_size(v_ids_2917_);
v___x_2928_ = lean_box_usize(v_sz_2927_);
v___x_2929_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1));
v___x_2930_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed), 12, 3);
lean_closure_set(v___x_2930_, 0, v___x_2928_);
lean_closure_set(v___x_2930_, 1, v___x_2929_);
lean_closure_set(v___x_2930_, 2, v_ids_2917_);
v___x_2931_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2930_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object* v_ids_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Elab_Tactic_getFVarIds(v_ids_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object* v_tac_2943_, lean_object* v_e_2944_, uint8_t v___x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_val_2956_; lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Elab_Tactic_elabTermForApply(v_e_2944_, v___x_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; uint8_t v___x_2984_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_2981_, v___y_2951_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = l_Lean_Expr_isMVar(v_a_2983_);
if (v___x_2984_ == 0)
{
v_val_2956_ = v_a_2983_;
goto v___jp_2955_;
}
else
{
uint8_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = 0;
v___x_2986_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2985_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2987_; lean_object* v_a_2988_; 
lean_dec_ref_known(v___x_2986_, 1);
v___x_2987_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_2983_, v___y_2951_);
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref(v___x_2987_);
v_val_2956_ = v_a_2988_;
goto v___jp_2955_;
}
else
{
lean_dec(v_a_2983_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v_tac_2943_);
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v_tac_2943_);
v_a_2989_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2980_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2980_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
v___jp_2955_:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2947_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
v___x_2959_ = lean_apply_7(v_tac_2943_, v_a_2958_, v_val_2956_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, lean_box(0));
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2961_ = 0;
v___x_2962_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2961_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v___x_2963_; 
lean_dec_ref_known(v___x_2962_, 1);
v___x_2963_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_2960_, v___y_2947_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v___x_2963_;
}
else
{
lean_dec(v_a_2960_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v___x_2962_;
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
v_a_2964_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2959_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2959_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec_ref(v_val_2956_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v_tac_2943_);
v_a_2972_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2957_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2957_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object* v_tac_2997_, lean_object* v_e_2998_, lean_object* v___x_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v___x_920__boxed_3009_; lean_object* v_res_3010_; 
v___x_920__boxed_3009_ = lean_unbox(v___x_2999_);
v_res_3010_ = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(v_tac_2997_, v_e_2998_, v___x_920__boxed_3009_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* v_tac_3011_, lean_object* v_e_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___f_3024_; lean_object* v___x_3025_; 
v___x_3022_ = 1;
v___x_3023_ = lean_box(v___x_3022_);
v___f_3024_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3024_, 0, v_tac_3011_);
lean_closure_set(v___f_3024_, 1, v_e_3012_);
lean_closure_set(v___f_3024_, 2, v___x_3023_);
v___x_3025_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3024_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object* v_tac_3026_, lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v_tac_3026_, v_e_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t v___x_3038_, lean_object* v_g_3039_, lean_object* v_e_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
uint8_t v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3046_ = 0;
v___x_3047_ = 0;
v___x_3048_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3048_, 0, v___x_3046_);
lean_ctor_set_uint8(v___x_3048_, 1, v___x_3038_);
lean_ctor_set_uint8(v___x_3048_, 2, v___x_3047_);
lean_ctor_set_uint8(v___x_3048_, 3, v___x_3038_);
v___x_3049_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
lean_inc_ref(v_e_3040_);
v___x_3050_ = l_Lean_MessageData_ofExpr(v_e_3040_);
v___x_3051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3049_);
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___x_3054_ = l_Lean_MVarId_apply(v_g_3039_, v_e_3040_, v___x_3048_, v___x_3053_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object* v___x_3055_, lean_object* v_g_3056_, lean_object* v_e_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v___x_160__boxed_3063_; lean_object* v_res_3064_; 
v___x_160__boxed_3063_ = lean_unbox(v___x_3055_);
v_res_3064_ = l_Lean_Elab_Tactic_evalApply___lam__0(v___x_160__boxed_3063_, v_g_3056_, v_e_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* v_stx_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
lean_inc(v_stx_3071_);
v___x_3082_ = l_Lean_Syntax_isOfKind(v_stx_3071_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec(v_stx_3071_);
v___x_3083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3084_ = lean_box(v___x_3082_);
v___f_3085_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3085_, 0, v___x_3084_);
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = l_Lean_Syntax_getArg(v_stx_3071_, v___x_3086_);
lean_dec(v_stx_3071_);
v___x_3088_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v___f_3085_, v___x_3087_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object* v_stx_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Elab_Tactic_evalApply(v_stx_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3107_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3108_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
v___x_3109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3110_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___boxed), 10, 0);
v___x_3111_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3107_, v___x_3108_, v___x_3109_, v___x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6));
v___x_3142_ = l_Lean_addBuiltinDeclarationRanges(v___x_3140_, v___x_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
return v_res_3144_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_box(0);
v___x_3146_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_3145_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(lean_object* v_00_u03b1_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(v_00_u03b1_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(lean_object* v_msg_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_ref_3173_; lean_object* v___x_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3183_; 
v_ref_3173_ = lean_ctor_get(v___y_3170_, 2);
v___x_3174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_inc(v_ref_3173_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_ref_3173_);
lean_ctor_set(v___x_3179_, 1, v_a_3175_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 1);
lean_ctor_set(v___x_3177_, 0, v___x_3179_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v_msg_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3190_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__1));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(lean_object* v___x_3195_, lean_object* v_ctor_3196_, lean_object* v_args_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__0));
v___x_3224_ = lean_string_dec_eq(v_ctor_3196_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = lean_array_get_size(v_args_3197_);
v___x_3227_ = lean_unsigned_to_nat(1u);
v___x_3228_ = lean_nat_dec_eq(v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v___x_3229_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2);
v___x_3230_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v___x_3229_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
goto v___jp_3203_;
}
}
v___jp_3203_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_unsigned_to_nat(0u);
v___x_3205_ = lean_array_get_borrowed(v___x_3195_, v_args_3197_, v___x_3204_);
lean_inc(v___x_3205_);
v___x_3206_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_3205_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
v_a_3215_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3206_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3206_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed(lean_object* v___x_3239_, lean_object* v_ctor_3240_, lean_object* v_args_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(v___x_3239_, v_ctor_3240_, v_args_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v_args_3241_);
lean_dec_ref(v_ctor_3240_);
lean_dec_ref(v___x_3239_);
return v_res_3247_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___f_3249_; 
v___x_3248_ = l_Lean_instInhabitedExpr;
v___f_3249_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3249_, 0, v___x_3248_);
return v___f_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___f_3262_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0);
v___x_3263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3264_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_3263_, v___f_3262_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___boxed(lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(lean_object* v_00_u03b1_3272_, lean_object* v_msg_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v_msg_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_3280_, lean_object* v_msg_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(v_00_u03b1_3280_, v_msg_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3291_ = l_Lean_Expr_const___override(v___x_3290_, v___x_3289_);
return v___x_3291_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2);
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__0));
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v___x_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig(void){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = l_Lean_Elab_abortTermExceptionId;
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v___x_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v___x_3309_; 
v___x_3309_ = l_Lean_Expr_hasMVar(v_e_3306_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_e_3306_);
return v___x_3310_;
}
else
{
lean_object* v___x_3311_; lean_object* v_mctx_3312_; lean_object* v___x_3313_; lean_object* v_fst_3314_; lean_object* v_snd_3315_; lean_object* v___x_3316_; lean_object* v_cache_3317_; lean_object* v_zetaDeltaFVarIds_3318_; lean_object* v_postponed_3319_; lean_object* v_diag_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3329_; 
v___x_3311_ = lean_st_ref_get(v___y_3307_);
v_mctx_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc_ref(v_mctx_3312_);
lean_dec(v___x_3311_);
v___x_3313_ = l_Lean_instantiateMVarsCore(v_mctx_3312_, v_e_3306_);
v_fst_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_fst_3314_);
v_snd_3315_ = lean_ctor_get(v___x_3313_, 1);
lean_inc(v_snd_3315_);
lean_dec_ref(v___x_3313_);
v___x_3316_ = lean_st_ref_take(v___y_3307_);
v_cache_3317_ = lean_ctor_get(v___x_3316_, 1);
v_zetaDeltaFVarIds_3318_ = lean_ctor_get(v___x_3316_, 2);
v_postponed_3319_ = lean_ctor_get(v___x_3316_, 3);
v_diag_3320_ = lean_ctor_get(v___x_3316_, 4);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3329_ == 0)
{
lean_object* v_unused_3330_; 
v_unused_3330_ = lean_ctor_get(v___x_3316_, 0);
lean_dec(v_unused_3330_);
v___x_3322_ = v___x_3316_;
v_isShared_3323_ = v_isSharedCheck_3329_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_diag_3320_);
lean_inc(v_postponed_3319_);
lean_inc(v_zetaDeltaFVarIds_3318_);
lean_inc(v_cache_3317_);
lean_dec(v___x_3316_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3329_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_snd_3315_);
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_snd_3315_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_cache_3317_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v_zetaDeltaFVarIds_3318_);
lean_ctor_set(v_reuseFailAlloc_3328_, 3, v_postponed_3319_);
lean_ctor_set(v_reuseFailAlloc_3328_, 4, v_diag_3320_);
v___x_3325_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_st_ref_put(v___y_3307_, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_fst_3314_);
return v___x_3327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3331_, v___y_3332_);
lean_dec(v___y_3332_);
return v_res_3334_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_opts_3335_, lean_object* v_opt_3336_){
_start:
{
lean_object* v_name_3337_; lean_object* v_defValue_3338_; lean_object* v_map_3339_; lean_object* v___x_3340_; 
v_name_3337_ = lean_ctor_get(v_opt_3336_, 0);
v_defValue_3338_ = lean_ctor_get(v_opt_3336_, 1);
v_map_3339_ = lean_ctor_get(v_opts_3335_, 0);
v___x_3340_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3339_, v_name_3337_);
if (lean_obj_tag(v___x_3340_) == 0)
{
uint8_t v___x_3341_; 
v___x_3341_ = lean_unbox(v_defValue_3338_);
return v___x_3341_;
}
else
{
lean_object* v_val_3342_; 
v_val_3342_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___x_3340_, 1);
if (lean_obj_tag(v_val_3342_) == 1)
{
uint8_t v_v_3343_; 
v_v_3343_ = lean_ctor_get_uint8(v_val_3342_, 0);
lean_dec_ref_known(v_val_3342_, 0);
return v_v_3343_;
}
else
{
uint8_t v___x_3344_; 
lean_dec(v_val_3342_);
v___x_3344_ = lean_unbox(v_defValue_3338_);
return v___x_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_3345_, lean_object* v_opt_3346_){
_start:
{
uint8_t v_res_3347_; lean_object* v_r_3348_; 
v_res_3347_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_3345_, v_opt_3346_);
lean_dec_ref(v_opt_3346_);
lean_dec_ref(v_opts_3345_);
v_r_3348_ = lean_box(v_res_3347_);
return v_r_3348_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_box(1);
v___x_3350_ = l_Lean_MessageData_ofFormat(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2));
v___x_3355_ = l_Lean_MessageData_ofFormat(v___x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object* v_x_3356_, lean_object* v_x_3357_){
_start:
{
if (lean_obj_tag(v_x_3357_) == 0)
{
return v_x_3356_;
}
else
{
lean_object* v_head_3358_; lean_object* v_tail_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3381_; 
v_head_3358_ = lean_ctor_get(v_x_3357_, 0);
v_tail_3359_ = lean_ctor_get(v_x_3357_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_x_3357_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3361_ = v_x_3357_;
v_isShared_3362_ = v_isSharedCheck_3381_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_tail_3359_);
lean_inc(v_head_3358_);
lean_dec(v_x_3357_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3381_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_before_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3379_; 
v_before_3363_ = lean_ctor_get(v_head_3358_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_head_3358_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v_head_3358_, 1);
lean_dec(v_unused_3380_);
v___x_3365_ = v_head_3358_;
v_isShared_3366_ = v_isSharedCheck_3379_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_before_3363_);
lean_dec(v_head_3358_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3379_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 7);
lean_ctor_set(v___x_3365_, 1, v___x_3367_);
lean_ctor_set(v___x_3365_, 0, v_x_3356_);
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_x_3356_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_3362_ == 0)
{
lean_ctor_set_tag(v___x_3361_, 7);
lean_ctor_set(v___x_3361_, 1, v___x_3370_);
lean_ctor_set(v___x_3361_, 0, v___x_3369_);
v___x_3372_ = v___x_3361_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = l_Lean_MessageData_ofSyntax(v_before_3363_);
v___x_3374_ = l_Lean_indentD(v___x_3373_);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3372_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v_x_3356_ = v___x_3375_;
v_x_3357_ = v_tail_3359_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_3386_ = l_Lean_MessageData_ofFormat(v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_3387_, lean_object* v_macroStack_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3389_);
v___x_3392_ = l_Lean_Elab_pp_macroStack;
v___x_3393_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_3391_, v___x_3392_);
lean_dec_ref(v___x_3391_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec(v_macroStack_3388_);
v___x_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_msgData_3387_);
return v___x_3394_;
}
else
{
if (lean_obj_tag(v_macroStack_3388_) == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v_msgData_3387_);
return v___x_3395_;
}
else
{
lean_object* v_head_3396_; lean_object* v_after_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3412_; 
v_head_3396_ = lean_ctor_get(v_macroStack_3388_, 0);
lean_inc(v_head_3396_);
v_after_3397_ = lean_ctor_get(v_head_3396_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_head_3396_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v_head_3396_, 0);
lean_dec(v_unused_3413_);
v___x_3399_ = v_head_3396_;
v_isShared_3400_ = v_isSharedCheck_3412_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_after_3397_);
lean_dec(v_head_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3412_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3401_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 7);
lean_ctor_set(v___x_3399_, 1, v___x_3401_);
lean_ctor_set(v___x_3399_, 0, v_msgData_3387_);
v___x_3403_ = v___x_3399_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_msgData_3387_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_msgData_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3404_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = l_Lean_MessageData_ofSyntax(v_after_3397_);
v___x_3407_ = l_Lean_indentD(v___x_3406_);
v_msgData_3408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3408_, 0, v___x_3405_);
lean_ctor_set(v_msgData_3408_, 1, v___x_3407_);
v___x_3409_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_3408_, v_macroStack_3388_);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3414_, lean_object* v_macroStack_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3414_, v_macroStack_3415_, v___y_3416_);
lean_dec_ref(v___y_3416_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_ref_3427_; lean_object* v_macroStack_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v_a_3431_; lean_object* v___x_3432_; lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3441_; 
v_ref_3427_ = lean_ctor_get(v___y_3424_, 2);
v_macroStack_3428_ = lean_ctor_get(v___y_3420_, 1);
v___x_3429_ = l_Lean_Elab_getBetterRef(v_ref_3427_, v_macroStack_3428_);
v___x_3430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_3419_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
lean_inc(v_macroStack_3428_);
v___x_3432_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_3431_, v_macroStack_3428_, v___y_3424_);
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3429_);
lean_ctor_set(v___x_3437_, 1, v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 1);
lean_ctor_set(v___x_3435_, 0, v___x_3437_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
return v_res_3450_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__0));
v___x_3453_ = l_Lean_stringToMessageData(v___x_3452_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1);
v___x_3455_ = l_Lean_MessageData_ofExpr(v___x_3454_);
return v___x_3455_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2);
v___x_3457_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v___x_3456_);
return v___x_3458_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_3460_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___x_3459_);
return v___x_3461_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__5));
v___x_3464_ = l_Lean_stringToMessageData(v___x_3463_);
return v___x_3464_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__7));
v___x_3467_ = l_Lean_stringToMessageData(v___x_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(lean_object* v_stx_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_ty_x3f_3476_; uint8_t v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v_toCold_3482_; lean_object* v_currRecDepth_3483_; lean_object* v_ref_3484_; uint16_t v_optionFlags_3485_; uint8_t v_suppressElabErrors_3486_; uint8_t v_isRecordingDeps_3487_; uint8_t v___x_3488_; lean_object* v_ref_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_ty_x3f_3476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2);
v___x_3477_ = 1;
v___x_3478_ = lean_box(0);
v___x_3479_ = lean_box(v___x_3477_);
v___x_3480_ = lean_box(v___x_3477_);
lean_inc(v_stx_3468_);
v___x_3481_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3481_, 0, v_stx_3468_);
lean_closure_set(v___x_3481_, 1, v_ty_x3f_3476_);
lean_closure_set(v___x_3481_, 2, v___x_3479_);
lean_closure_set(v___x_3481_, 3, v___x_3480_);
lean_closure_set(v___x_3481_, 4, v___x_3478_);
v_toCold_3482_ = lean_ctor_get(v_a_3473_, 0);
v_currRecDepth_3483_ = lean_ctor_get(v_a_3473_, 1);
v_ref_3484_ = lean_ctor_get(v_a_3473_, 2);
v_optionFlags_3485_ = lean_ctor_get_uint16(v_a_3473_, sizeof(void*)*3);
v_suppressElabErrors_3486_ = lean_ctor_get_uint8(v_a_3473_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3487_ = lean_ctor_get_uint8(v_a_3473_, sizeof(void*)*3 + 3);
v___x_3488_ = 1;
v_ref_3489_ = l_Lean_replaceRef(v_stx_3468_, v_ref_3484_);
lean_dec(v_stx_3468_);
lean_inc(v_currRecDepth_3483_);
lean_inc_ref(v_toCold_3482_);
v___x_3490_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3490_, 0, v_toCold_3482_);
lean_ctor_set(v___x_3490_, 1, v_currRecDepth_3483_);
lean_ctor_set(v___x_3490_, 2, v_ref_3489_);
lean_ctor_set_uint16(v___x_3490_, sizeof(void*)*3, v_optionFlags_3485_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*3 + 2, v_suppressElabErrors_3486_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*3 + 3, v_isRecordingDeps_3487_);
v___x_3491_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3481_, v___x_3488_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v___x_3490_, v_a_3474_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v_a_3494_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; uint8_t v___x_3578_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_3492_, v_a_3472_);
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3493_);
v___x_3578_ = l_Lean_Expr_hasSorry(v_a_3494_);
if (v___x_3578_ == 0)
{
v___y_3523_ = v_a_3469_;
v___y_3524_ = v_a_3470_;
v___y_3525_ = v_a_3471_;
v___y_3526_ = v_a_3472_;
v___y_3527_ = v___x_3490_;
v___y_3528_ = v_a_3474_;
goto v___jp_3522_;
}
else
{
uint8_t v___x_3579_; 
v___x_3579_ = l_Lean_Expr_hasSyntheticSorry(v_a_3494_);
if (v___x_3579_ == 0)
{
v___y_3560_ = v_a_3469_;
v___y_3561_ = v_a_3470_;
v___y_3562_ = v_a_3471_;
v___y_3563_ = v_a_3472_;
v___y_3564_ = v___x_3490_;
v___y_3565_ = v_a_3474_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3580_; lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_a_3494_);
lean_dec_ref_known(v___x_3490_, 3);
v___x_3580_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
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
v___jp_3495_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3494_);
v___x_3503_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(v_a_3494_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_dec_ref(v___y_3500_);
lean_dec(v_a_3494_);
return v___x_3503_;
}
else
{
lean_object* v_a_3504_; uint8_t v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
v___x_3505_ = l_Lean_Exception_isInterrupt(v_a_3504_);
if (v___x_3505_ == 0)
{
uint8_t v___x_3506_; 
lean_inc(v_a_3504_);
v___x_3506_ = l_Lean_Exception_isRuntime(v_a_3504_);
if (v___x_3506_ == 0)
{
if (lean_obj_tag(v_a_3504_) == 0)
{
lean_dec_ref_known(v_a_3504_, 2);
lean_dec_ref(v___y_3500_);
lean_dec(v_a_3494_);
return v___x_3503_;
}
else
{
lean_object* v_id_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3520_; 
v_id_3507_ = lean_ctor_get(v_a_3504_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; 
v_unused_3521_ = lean_ctor_get(v_a_3504_, 1);
lean_dec(v_unused_3521_);
v___x_3509_ = v_a_3504_;
v_isShared_3510_ = v_isSharedCheck_3520_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_id_3507_);
lean_dec(v_a_3504_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3520_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
uint8_t v___x_3511_; 
v___x_3511_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3502_, v_id_3507_);
lean_dec(v_id_3507_);
if (v___x_3511_ == 0)
{
lean_del_object(v___x_3509_);
lean_dec_ref(v___y_3500_);
lean_dec(v_a_3494_);
return v___x_3503_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3512_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4);
v___x_3513_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6);
v___x_3514_ = l_Lean_indentExpr(v_a_3494_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set_tag(v___x_3509_, 7);
lean_ctor_set(v___x_3509_, 1, v___x_3514_);
lean_ctor_set(v___x_3509_, 0, v___x_3513_);
v___x_3516_ = v___x_3509_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v___x_3512_);
v___x_3518_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3517_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec_ref(v___y_3500_);
return v___x_3518_;
}
}
}
}
}
else
{
lean_dec(v_a_3504_);
lean_dec_ref(v___y_3500_);
lean_dec(v_a_3494_);
return v___x_3503_;
}
}
else
{
lean_dec(v_a_3504_);
lean_dec_ref(v___y_3500_);
lean_dec(v_a_3494_);
return v___x_3503_;
}
}
}
v___jp_3522_:
{
lean_object* v___x_3529_; 
lean_inc(v_a_3494_);
v___x_3529_ = l_Lean_Meta_getMVars(v_a_3494_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v___x_3531_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3530_, v___x_3478_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
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
v___y_3496_ = v___y_3523_;
v___y_3497_ = v___y_3524_;
v___y_3498_ = v___y_3525_;
v___y_3499_ = v___y_3526_;
v___y_3500_ = v___y_3527_;
v___y_3501_ = v___y_3528_;
goto v___jp_3495_;
}
else
{
lean_object* v___x_3534_; lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v___y_3527_);
lean_dec(v_a_3494_);
v___x_3534_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
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
lean_dec(v_a_3494_);
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
lean_dec(v_a_3494_);
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
v___x_3566_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8);
v___x_3567_ = l_Lean_indentExpr(v_a_3494_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3568_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
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
lean_dec_ref_known(v___x_3490_, 3);
v_a_3589_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3491_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3491_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(v_stx_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(uint8_t v_config_3616_, lean_object* v_item_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_item_3626_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3630_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3617_, v___x_3629_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3630_) == 0)
{
uint8_t v___x_3631_; 
lean_dec_ref_known(v___x_3630_, 1);
v___x_3631_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3617_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3632_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3617_);
lean_inc_ref(v_item_3617_);
v___x_3633_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3617_);
v___x_3634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__1));
v___x_3635_ = lean_string_dec_eq(v___x_3632_, v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2));
v___x_3637_ = lean_string_dec_eq(v___x_3632_, v___x_3636_);
lean_dec_ref(v___x_3632_);
if (v___x_3637_ == 0)
{
lean_dec_ref(v_item_3617_);
v_item_3626_ = v___x_3633_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3));
v___x_3639_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3617_, v___x_3638_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3639_) == 0)
{
uint8_t v___x_3640_; 
lean_dec_ref_known(v___x_3639_, 1);
v___x_3640_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3633_);
if (v___x_3640_ == 0)
{
lean_dec_ref(v_item_3617_);
v_item_3626_ = v___x_3633_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3641_; 
lean_dec_ref(v___x_3633_);
v___x_3641_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
v_a_3650_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3641_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3641_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref(v___x_3633_);
lean_dec_ref(v_item_3617_);
v_a_3658_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3639_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3639_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
else
{
uint8_t v___x_3666_; 
lean_dec_ref(v___x_3632_);
v___x_3666_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3633_);
if (v___x_3666_ == 0)
{
lean_dec_ref(v_item_3617_);
v_item_3626_ = v___x_3633_;
goto v___jp_3625_;
}
else
{
lean_object* v_value_3667_; lean_object* v___x_3668_; 
lean_dec_ref(v___x_3633_);
v_value_3667_ = lean_ctor_get(v_item_3617_, 2);
lean_inc(v_value_3667_);
lean_dec_ref(v_item_3617_);
v___x_3668_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(v_value_3667_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v___x_3668_;
}
}
}
else
{
v_item_3626_ = v_item_3617_;
goto v___jp_3625_;
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec_ref(v_item_3617_);
v_a_3669_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3630_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3630_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
v___jp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__0));
v___x_3628_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3626_, v___x_3627_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v___x_3628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3677_, lean_object* v_item_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
uint8_t v_config_3624__boxed_3686_; lean_object* v_res_3687_; 
v_config_3624__boxed_3686_ = lean_unbox(v_config_3677_);
v_res_3687_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(v_config_3624__boxed_3686_, v_item_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3690_, v___y_3694_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(v_e_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_3726_, lean_object* v_msg_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3736_, lean_object* v_msg_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_3736_, v_msg_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_3746_, lean_object* v_macroStack_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3746_, v_macroStack_3747_, v___y_3752_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_3756_, lean_object* v_macroStack_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_3756_, v_macroStack_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3765_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3766_ = lean_box(0);
v___x_3767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3768_ = l_Lean_mkConst(v___x_3767_, v___x_3766_);
return v___x_3768_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0);
v___x_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(uint8_t v_cfg_3771_, lean_object* v_cfgItem_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3780_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1);
v___x_3781_ = lean_box(v_cfg_3771_);
v___x_3782_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v___x_3781_, v_cfgItem_3772_, v___x_3780_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___boxed(lean_object* v_cfg_3783_, lean_object* v_cfgItem_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
uint8_t v_cfg_boxed_3792_; lean_object* v_res_3793_; 
v_cfg_boxed_3792_ = lean_unbox(v_cfg_3783_);
v_res_3793_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(v_cfg_boxed_3792_, v_cfgItem_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v_cfgItem_3784_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg(lean_object* v_cfg_3795_, uint8_t v_init_3796_, uint8_t v_logExceptions_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_onErr_3802_; lean_object* v_eval_3803_; 
v_onErr_3802_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConstructorConfig___redArg___closed__0));
v_eval_3803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0));
if (v_logExceptions_3797_ == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_box(v_init_3796_);
v___x_3805_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3803_, v___x_3804_, v_cfg_3795_, v_onErr_3802_, v_logExceptions_3797_, v_a_3799_, v_a_3800_);
return v___x_3805_;
}
else
{
uint8_t v_recover_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_recover_3806_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*1);
v___x_3807_ = lean_box(v_init_3796_);
v___x_3808_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3803_, v___x_3807_, v_cfg_3795_, v_onErr_3802_, v_recover_3806_, v_a_3799_, v_a_3800_);
return v___x_3808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___boxed(lean_object* v_cfg_3809_, lean_object* v_init_3810_, lean_object* v_logExceptions_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
uint8_t v_init_boxed_3816_; uint8_t v_logExceptions_boxed_3817_; lean_object* v_res_3818_; 
v_init_boxed_3816_ = lean_unbox(v_init_3810_);
v_logExceptions_boxed_3817_ = lean_unbox(v_logExceptions_3811_);
v_res_3818_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v_cfg_3809_, v_init_boxed_3816_, v_logExceptions_boxed_3817_, v_a_3812_, v_a_3813_, v_a_3814_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec_ref(v_a_3812_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig(lean_object* v_cfg_3819_, uint8_t v_init_3820_, uint8_t v_logExceptions_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v_cfg_3819_, v_init_3820_, v_logExceptions_3821_, v_a_3822_, v_a_3828_, v_a_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___boxed(lean_object* v_cfg_3832_, lean_object* v_init_3833_, lean_object* v_logExceptions_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
uint8_t v_init_boxed_3844_; uint8_t v_logExceptions_boxed_3845_; lean_object* v_res_3846_; 
v_init_boxed_3844_ = lean_unbox(v_init_3833_);
v_logExceptions_boxed_3845_ = lean_unbox(v_logExceptions_3834_);
v_res_3846_ = l_Lean_Elab_Tactic_elabConstructorConfig(v_cfg_3832_, v_init_boxed_3844_, v_logExceptions_boxed_3845_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
if (lean_obj_tag(v_a_3847_) == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = l_List_reverse___redArg(v_a_3848_);
return v___x_3849_;
}
else
{
lean_object* v_head_3850_; lean_object* v_tail_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3864_; 
v_head_3850_ = lean_ctor_get(v_a_3847_, 0);
v_tail_3851_ = lean_ctor_get(v_a_3847_, 1);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3853_ = v_a_3847_;
v_isShared_3854_ = v_isSharedCheck_3864_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_tail_3851_);
lean_inc(v_head_3850_);
lean_dec(v_a_3847_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3864_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
uint8_t v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3855_ = 0;
v___x_3856_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_3857_ = l_Lean_MessageData_ofConstName(v_head_3850_, v___x_3855_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
lean_ctor_set(v___x_3859_, 1, v___x_3856_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 1, v_a_3848_);
lean_ctor_set(v___x_3853_, 0, v___x_3859_);
v___x_3861_ = v___x_3853_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_a_3848_);
v___x_3861_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
v_a_3847_ = v_tail_3851_;
v_a_3848_ = v___x_3861_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3870_, lean_object* v_x_3871_){
_start:
{
if (lean_obj_tag(v_x_3871_) == 1)
{
lean_object* v_pre_3872_; 
v_pre_3872_ = lean_ctor_get(v_x_3871_, 0);
switch(lean_obj_tag(v_pre_3872_))
{
case 1:
{
lean_object* v_pre_3873_; 
v_pre_3873_ = lean_ctor_get(v_pre_3872_, 0);
switch(lean_obj_tag(v_pre_3873_))
{
case 0:
{
lean_object* v_str_3874_; lean_object* v_str_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v_str_3874_ = lean_ctor_get(v_x_3871_, 1);
v_str_3875_ = lean_ctor_get(v_pre_3872_, 1);
v___x_3876_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1));
v___x_3877_ = lean_string_dec_eq(v_str_3875_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__2));
v___x_3879_ = lean_string_dec_eq(v_str_3875_, v___x_3878_);
if (v___x_3879_ == 0)
{
return v___x_3879_;
}
else
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3880_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__0));
v___x_3881_ = lean_string_dec_eq(v_str_3874_, v___x_3880_);
if (v___x_3881_ == 0)
{
return v___x_3881_;
}
else
{
return v_suppressElabErrors_3870_;
}
}
}
else
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__1));
v___x_3883_ = lean_string_dec_eq(v_str_3874_, v___x_3882_);
if (v___x_3883_ == 0)
{
return v___x_3883_;
}
else
{
return v_suppressElabErrors_3870_;
}
}
}
case 1:
{
lean_object* v_pre_3884_; 
v_pre_3884_ = lean_ctor_get(v_pre_3873_, 0);
if (lean_obj_tag(v_pre_3884_) == 0)
{
lean_object* v_str_3885_; lean_object* v_str_3886_; lean_object* v_str_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_str_3885_ = lean_ctor_get(v_x_3871_, 1);
v_str_3886_ = lean_ctor_get(v_pre_3872_, 1);
v_str_3887_ = lean_ctor_get(v_pre_3873_, 1);
v___x_3888_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__2));
v___x_3889_ = lean_string_dec_eq(v_str_3887_, v___x_3888_);
if (v___x_3889_ == 0)
{
return v___x_3889_;
}
else
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__3));
v___x_3891_ = lean_string_dec_eq(v_str_3886_, v___x_3890_);
if (v___x_3891_ == 0)
{
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__4));
v___x_3893_ = lean_string_dec_eq(v_str_3885_, v___x_3892_);
if (v___x_3893_ == 0)
{
return v___x_3893_;
}
else
{
return v_suppressElabErrors_3870_;
}
}
}
}
else
{
uint8_t v___x_3894_; 
v___x_3894_ = 0;
return v___x_3894_;
}
}
default: 
{
uint8_t v___x_3895_; 
v___x_3895_ = 0;
return v___x_3895_;
}
}
}
case 0:
{
lean_object* v_str_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v_str_3896_ = lean_ctor_get(v_x_3871_, 1);
v___x_3897_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0));
v___x_3898_ = lean_string_dec_eq(v_str_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
return v___x_3898_;
}
else
{
return v_suppressElabErrors_3870_;
}
}
default: 
{
uint8_t v___x_3899_; 
v___x_3899_ = 0;
return v___x_3899_;
}
}
}
else
{
uint8_t v___x_3900_; 
v___x_3900_ = 0;
return v___x_3900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3901_, lean_object* v_x_3902_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3903_; uint8_t v_res_3904_; lean_object* v_r_3905_; 
v_suppressElabErrors_boxed_3903_ = lean_unbox(v_suppressElabErrors_3901_);
v_res_3904_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3903_, v_x_3902_);
lean_dec(v_x_3902_);
v_r_3905_ = lean_box(v_res_3904_);
return v_r_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_3907_, lean_object* v_msgData_3908_, uint8_t v_severity_3909_, uint8_t v_isSilent_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___y_3917_; lean_object* v___y_3918_; uint8_t v___y_3919_; uint8_t v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v_toCold_3924_; lean_object* v___y_3925_; lean_object* v___y_3954_; lean_object* v___y_3955_; uint8_t v___y_3956_; uint8_t v___y_3957_; lean_object* v___y_3958_; uint8_t v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3981_; lean_object* v___y_3982_; uint8_t v___y_3983_; lean_object* v___y_3984_; uint8_t v___y_3985_; uint8_t v___y_3986_; lean_object* v___y_3987_; uint8_t v___y_3991_; uint8_t v___y_3992_; uint8_t v___x_4002_; uint8_t v___y_4004_; uint8_t v___x_4010_; 
v___x_4002_ = 2;
v___x_4010_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3909_, v___x_4002_);
if (v___x_4010_ == 0)
{
v___y_4004_ = v___x_4010_;
goto v___jp_4003_;
}
else
{
uint8_t v___x_4011_; 
lean_inc_ref(v_msgData_3908_);
v___x_4011_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3908_);
if (v___x_4011_ == 0)
{
v___y_4004_ = v___x_4011_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_dec_ref(v_msgData_3908_);
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
v___jp_3916_:
{
lean_object* v_currNamespace_3926_; lean_object* v_openDecls_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_env_3932_; lean_object* v_nextMacroScope_3933_; lean_object* v_ngen_3934_; lean_object* v_auxDeclNGen_3935_; lean_object* v_traceState_3936_; lean_object* v_cache_3937_; lean_object* v_recordedDeps_3938_; lean_object* v_messages_3939_; lean_object* v_infoState_3940_; lean_object* v_snapshotTasks_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3952_; 
v_currNamespace_3926_ = lean_ctor_get(v_toCold_3924_, 4);
v_openDecls_3927_ = lean_ctor_get(v_toCold_3924_, 5);
lean_inc(v_openDecls_3927_);
lean_inc(v_currNamespace_3926_);
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v_currNamespace_3926_);
lean_ctor_set(v___x_3928_, 1, v_openDecls_3927_);
v___x_3929_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___y_3923_);
lean_inc_ref(v___y_3921_);
lean_inc_ref(v___y_3922_);
v___x_3930_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3930_, 0, v___y_3922_);
lean_ctor_set(v___x_3930_, 1, v___y_3917_);
lean_ctor_set(v___x_3930_, 2, v___y_3918_);
lean_ctor_set(v___x_3930_, 3, v___y_3921_);
lean_ctor_set(v___x_3930_, 4, v___x_3929_);
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*5, v___y_3919_);
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*5 + 1, v___y_3920_);
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*5 + 2, v_isSilent_3910_);
v___x_3931_ = lean_st_ref_take(v___y_3925_);
v_env_3932_ = lean_ctor_get(v___x_3931_, 0);
v_nextMacroScope_3933_ = lean_ctor_get(v___x_3931_, 1);
v_ngen_3934_ = lean_ctor_get(v___x_3931_, 2);
v_auxDeclNGen_3935_ = lean_ctor_get(v___x_3931_, 3);
v_traceState_3936_ = lean_ctor_get(v___x_3931_, 4);
v_cache_3937_ = lean_ctor_get(v___x_3931_, 5);
v_recordedDeps_3938_ = lean_ctor_get(v___x_3931_, 6);
v_messages_3939_ = lean_ctor_get(v___x_3931_, 7);
v_infoState_3940_ = lean_ctor_get(v___x_3931_, 8);
v_snapshotTasks_3941_ = lean_ctor_get(v___x_3931_, 9);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3943_ = v___x_3931_;
v_isShared_3944_ = v_isSharedCheck_3952_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_snapshotTasks_3941_);
lean_inc(v_infoState_3940_);
lean_inc(v_messages_3939_);
lean_inc(v_recordedDeps_3938_);
lean_inc(v_cache_3937_);
lean_inc(v_traceState_3936_);
lean_inc(v_auxDeclNGen_3935_);
lean_inc(v_ngen_3934_);
lean_inc(v_nextMacroScope_3933_);
lean_inc(v_env_3932_);
lean_dec(v___x_3931_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3952_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3945_ = lean_box(0);
v___x_3946_ = l_Lean_MessageLog_add(v___x_3930_, v_messages_3939_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 7, v___x_3946_);
v___x_3948_ = v___x_3943_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_env_3932_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_nextMacroScope_3933_);
lean_ctor_set(v_reuseFailAlloc_3951_, 2, v_ngen_3934_);
lean_ctor_set(v_reuseFailAlloc_3951_, 3, v_auxDeclNGen_3935_);
lean_ctor_set(v_reuseFailAlloc_3951_, 4, v_traceState_3936_);
lean_ctor_set(v_reuseFailAlloc_3951_, 5, v_cache_3937_);
lean_ctor_set(v_reuseFailAlloc_3951_, 6, v_recordedDeps_3938_);
lean_ctor_set(v_reuseFailAlloc_3951_, 7, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3951_, 8, v_infoState_3940_);
lean_ctor_set(v_reuseFailAlloc_3951_, 9, v_snapshotTasks_3941_);
v___x_3948_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_st_ref_put(v___y_3925_, v___x_3948_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3945_);
return v___x_3950_;
}
}
}
v___jp_3953_:
{
lean_object* v_fileName_3962_; lean_object* v_fileMap_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3979_; 
v_fileName_3962_ = lean_ctor_get(v___y_3958_, 0);
v_fileMap_3963_ = lean_ctor_get(v___y_3958_, 1);
v___x_3964_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3908_);
v___x_3965_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v___x_3964_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3979_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3979_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_inc_ref_n(v_fileMap_3963_, 2);
v___x_3970_ = l_Lean_FileMap_toPosition(v_fileMap_3963_, v___y_3960_);
lean_dec(v___y_3960_);
v___x_3971_ = l_Lean_FileMap_toPosition(v_fileMap_3963_, v___y_3961_);
lean_dec(v___y_3961_);
v___x_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___closed__0));
if (v___y_3956_ == 0)
{
lean_del_object(v___x_3968_);
lean_dec_ref(v___y_3954_);
v___y_3917_ = v___x_3970_;
v___y_3918_ = v___x_3972_;
v___y_3919_ = v___y_3957_;
v___y_3920_ = v___y_3959_;
v___y_3921_ = v___x_3973_;
v___y_3922_ = v_fileName_3962_;
v___y_3923_ = v_a_3966_;
v_toCold_3924_ = v___y_3955_;
v___y_3925_ = v___y_3914_;
goto v___jp_3916_;
}
else
{
uint8_t v___x_3974_; 
lean_inc(v_a_3966_);
v___x_3974_ = l_Lean_MessageData_hasTag(v___y_3954_, v_a_3966_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
lean_dec_ref_known(v___x_3972_, 1);
lean_dec_ref(v___x_3970_);
lean_dec(v_a_3966_);
v___x_3975_ = lean_box(0);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3975_);
v___x_3977_ = v___x_3968_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
else
{
lean_del_object(v___x_3968_);
v___y_3917_ = v___x_3970_;
v___y_3918_ = v___x_3972_;
v___y_3919_ = v___y_3957_;
v___y_3920_ = v___y_3959_;
v___y_3921_ = v___x_3973_;
v___y_3922_ = v_fileName_3962_;
v___y_3923_ = v_a_3966_;
v_toCold_3924_ = v___y_3955_;
v___y_3925_ = v___y_3914_;
goto v___jp_3916_;
}
}
}
}
v___jp_3980_:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_Syntax_getTailPos_x3f(v___y_3984_, v___y_3985_);
lean_dec(v___y_3984_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_inc(v___y_3987_);
v___y_3954_ = v___y_3981_;
v___y_3955_ = v___y_3982_;
v___y_3956_ = v___y_3983_;
v___y_3957_ = v___y_3985_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3986_;
v___y_3960_ = v___y_3987_;
v___y_3961_ = v___y_3987_;
goto v___jp_3953_;
}
else
{
lean_object* v_val_3989_; 
v_val_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_val_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___y_3954_ = v___y_3981_;
v___y_3955_ = v___y_3982_;
v___y_3956_ = v___y_3983_;
v___y_3957_ = v___y_3985_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3986_;
v___y_3960_ = v___y_3987_;
v___y_3961_ = v_val_3989_;
goto v___jp_3953_;
}
}
v___jp_3990_:
{
lean_object* v_toCold_3993_; lean_object* v_ref_3994_; uint8_t v_suppressElabErrors_3995_; lean_object* v___x_3996_; lean_object* v___f_3997_; lean_object* v_ref_3998_; lean_object* v___x_3999_; 
v_toCold_3993_ = lean_ctor_get(v___y_3913_, 0);
v_ref_3994_ = lean_ctor_get(v___y_3913_, 2);
v_suppressElabErrors_3995_ = lean_ctor_get_uint8(v___y_3913_, sizeof(void*)*3 + 2);
v___x_3996_ = lean_box(v_suppressElabErrors_3995_);
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3997_, 0, v___x_3996_);
v_ref_3998_ = l_Lean_replaceRef(v_ref_3907_, v_ref_3994_);
v___x_3999_ = l_Lean_Syntax_getPos_x3f(v_ref_3998_, v___y_3991_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_unsigned_to_nat(0u);
v___y_3981_ = v___f_3997_;
v___y_3982_ = v_toCold_3993_;
v___y_3983_ = v_suppressElabErrors_3995_;
v___y_3984_ = v_ref_3998_;
v___y_3985_ = v___y_3991_;
v___y_3986_ = v___y_3992_;
v___y_3987_ = v___x_4000_;
goto v___jp_3980_;
}
else
{
lean_object* v_val_4001_; 
v_val_4001_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_val_4001_);
lean_dec_ref_known(v___x_3999_, 1);
v___y_3981_ = v___f_3997_;
v___y_3982_ = v_toCold_3993_;
v___y_3983_ = v_suppressElabErrors_3995_;
v___y_3984_ = v_ref_3998_;
v___y_3985_ = v___y_3991_;
v___y_3986_ = v___y_3992_;
v___y_3987_ = v_val_4001_;
goto v___jp_3980_;
}
}
v___jp_4003_:
{
uint8_t v___x_4005_; uint8_t v___x_4006_; 
v___x_4005_ = 1;
v___x_4006_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3909_, v___x_4005_);
if (v___x_4006_ == 0)
{
v___y_3991_ = v___y_4004_;
v___y_3992_ = v_severity_3909_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4007_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3913_);
v___x_4008_ = l_Lean_warningAsError;
v___x_4009_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_4007_, v___x_4008_);
lean_dec_ref(v___x_4007_);
if (v___x_4009_ == 0)
{
v___y_3991_ = v___y_4004_;
v___y_3992_ = v_severity_3909_;
goto v___jp_3990_;
}
else
{
v___y_3991_ = v___y_4004_;
v___y_3992_ = v___x_4002_;
goto v___jp_3990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_4014_, lean_object* v_msgData_4015_, lean_object* v_severity_4016_, lean_object* v_isSilent_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
uint8_t v_severity_boxed_4023_; uint8_t v_isSilent_boxed_4024_; lean_object* v_res_4025_; 
v_severity_boxed_4023_ = lean_unbox(v_severity_4016_);
v_isSilent_boxed_4024_ = lean_unbox(v_isSilent_4017_);
v_res_4025_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4014_, v_msgData_4015_, v_severity_boxed_4023_, v_isSilent_boxed_4024_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v_ref_4014_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(lean_object* v_msgData_4026_, uint8_t v_severity_4027_, uint8_t v_isSilent_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_ref_4038_; lean_object* v___x_4039_; 
v_ref_4038_ = lean_ctor_get(v___y_4035_, 2);
v___x_4039_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4038_, v_msgData_4026_, v_severity_4027_, v_isSilent_4028_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1___boxed(lean_object* v_msgData_4040_, lean_object* v_severity_4041_, lean_object* v_isSilent_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
uint8_t v_severity_boxed_4052_; uint8_t v_isSilent_boxed_4053_; lean_object* v_res_4054_; 
v_severity_boxed_4052_ = lean_unbox(v_severity_4041_);
v_isSilent_boxed_4053_ = lean_unbox(v_isSilent_4042_);
v_res_4054_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(v_msgData_4040_, v_severity_boxed_4052_, v_isSilent_boxed_4053_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(lean_object* v_msgData_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
uint8_t v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = 1;
v___x_4066_ = 0;
v___x_4067_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(v_msgData_4055_, v___x_4065_, v___x_4066_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1___boxed(lean_object* v_msgData_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(v_msgData_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
return v_res_4078_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__0));
v___x_4081_ = l_Lean_stringToMessageData(v___x_4080_);
return v___x_4081_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4093_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__6));
v___x_4094_ = l_Lean_stringToMessageData(v___x_4093_);
return v___x_4094_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__8));
v___x_4097_ = l_Lean_stringToMessageData(v___x_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__10));
v___x_4100_ = l_Lean_stringToMessageData(v___x_4099_);
return v___x_4100_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__12));
v___x_4103_ = l_Lean_stringToMessageData(v___x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(lean_object* v_stx_4106_, lean_object* v___x_4107_, uint8_t v_cfg_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4110_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; uint8_t v___x_4120_; uint8_t v___x_4121_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___x_4144_; uint8_t v___y_4146_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4120_ = 1;
v___x_4121_ = 0;
v___x_4144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__2));
if (v_cfg_4108_ == 0)
{
v___y_4146_ = v___x_4120_;
goto v___jp_4145_;
}
else
{
v___y_4146_ = v___x_4121_;
goto v___jp_4145_;
}
v___jp_4122_:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4121_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v___x_4132_; 
lean_dec_ref_known(v___x_4131_, 1);
v___x_4132_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___y_4123_, v___y_4124_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
return v___x_4132_;
}
else
{
lean_dec(v___y_4123_);
return v___x_4131_;
}
}
v___jp_4133_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_inc_ref(v___y_4137_);
v___x_4138_ = l_Lean_stringToMessageData(v___y_4137_);
v___x_4139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___y_4136_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1);
v___x_4141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4139_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
lean_ctor_set(v___x_4142_, 1, v___y_4134_);
v___x_4143_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(v___x_4142_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_dec_ref_known(v___x_4143_, 1);
v___y_4123_ = v___y_4135_;
v___y_4124_ = v___y_4110_;
v___y_4125_ = v___y_4111_;
v___y_4126_ = v___y_4112_;
v___y_4127_ = v___y_4113_;
v___y_4128_ = v___y_4114_;
v___y_4129_ = v___y_4115_;
v___y_4130_ = v___y_4116_;
goto v___jp_4122_;
}
else
{
lean_dec(v___y_4135_);
return v___x_4143_;
}
}
v___jp_4145_:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_MVarId_constructorCore(v_a_4119_, v___x_4144_, v___y_4146_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v_fst_4149_; lean_object* v_snd_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4197_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v_fst_4149_ = lean_ctor_get(v_a_4148_, 0);
v_snd_4150_ = lean_ctor_get(v_a_4148_, 1);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_a_4148_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4152_ = v_a_4148_;
v_isShared_4153_ = v_isSharedCheck_4197_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_snd_4150_);
lean_inc(v_fst_4149_);
lean_dec(v_a_4148_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4197_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4154_ = lean_unsigned_to_nat(1u);
v___x_4155_ = lean_array_get_size(v_snd_4150_);
v___x_4156_ = lean_nat_dec_lt(v___x_4154_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_del_object(v___x_4152_);
lean_dec(v_snd_4150_);
v___y_4123_ = v_fst_4149_;
v___y_4124_ = v___y_4110_;
v___y_4125_ = v___y_4111_;
v___y_4126_ = v___y_4112_;
v___y_4127_ = v___y_4113_;
v___y_4128_ = v___y_4114_;
v___y_4129_ = v___y_4115_;
v___y_4130_ = v___y_4116_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_inc(v_snd_4150_);
v___x_4157_ = lean_array_to_list(v_snd_4150_);
v___x_4158_ = l_List_drop___redArg(v___x_4154_, v___x_4157_);
lean_dec(v___x_4157_);
v___x_4159_ = lean_box(0);
lean_inc(v___x_4158_);
v___x_4160_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(v___x_4158_, v___x_4159_);
v___x_4161_ = l_Lean_MessageData_andList(v___x_4160_);
v___x_4162_ = lean_box(0);
v___x_4163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__5));
v___x_4164_ = lean_unsigned_to_nat(0u);
v___x_4165_ = l_Lean_Syntax_getArg(v_stx_4106_, v___x_4164_);
v___x_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
v___x_4167_ = 4;
v___x_4168_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4168_, 0, v___x_4163_);
lean_ctor_set(v___x_4168_, 1, v___x_4166_);
lean_ctor_set(v___x_4168_, 2, v___x_4162_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*3, v___x_4167_);
v___x_4169_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7);
v___x_4170_ = lean_mk_empty_array_with_capacity(v___x_4154_);
v___x_4171_ = lean_array_push(v___x_4170_, v___x_4168_);
v___x_4172_ = l_Lean_MessageData_hint(v___x_4169_, v___x_4171_, v___x_4162_, v___x_4162_, v___x_4121_, v___y_4115_, v___y_4116_);
lean_dec_ref(v___x_4171_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v___x_4174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9);
v___x_4175_ = lean_array_get(v___x_4107_, v_snd_4150_, v___x_4164_);
lean_dec(v_snd_4150_);
v___x_4176_ = l_Lean_MessageData_ofConstName(v___x_4175_, v___x_4121_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set_tag(v___x_4152_, 7);
lean_ctor_set(v___x_4152_, 1, v___x_4176_);
lean_ctor_set(v___x_4152_, 0, v___x_4174_);
v___x_4178_ = v___x_4152_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4174_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11);
v___x_4180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4178_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v___x_4161_);
v___x_4182_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13);
v___x_4183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4181_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
v___x_4184_ = l_List_lengthTR___redArg(v___x_4158_);
lean_dec(v___x_4158_);
v___x_4185_ = lean_nat_dec_eq(v___x_4184_, v___x_4154_);
lean_dec(v___x_4184_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; 
v___x_4186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__14));
v___y_4134_ = v_a_4173_;
v___y_4135_ = v_fst_4149_;
v___y_4136_ = v___x_4183_;
v___y_4137_ = v___x_4186_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4187_; 
v___x_4187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__15));
v___y_4134_ = v_a_4173_;
v___y_4135_ = v_fst_4149_;
v___y_4136_ = v___x_4183_;
v___y_4137_ = v___x_4187_;
goto v___jp_4133_;
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v___x_4161_);
lean_dec(v___x_4158_);
lean_del_object(v___x_4152_);
lean_dec(v_snd_4150_);
lean_dec(v_fst_4149_);
v_a_4189_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4172_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4172_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_a_4198_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4147_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4147_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_a_4206_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4118_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4118_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed(lean_object* v_stx_4214_, lean_object* v___x_4215_, lean_object* v_cfg_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v_cfg_boxed_4226_; lean_object* v_res_4227_; 
v_cfg_boxed_4226_ = lean_unbox(v_cfg_4216_);
v_res_4227_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(v_stx_4214_, v___x_4215_, v_cfg_boxed_4226_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___x_4215_);
lean_dec(v_stx_4214_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(lean_object* v_stx_4228_, uint8_t v_cfg_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___f_4241_; lean_object* v___x_4242_; 
v___x_4239_ = lean_box(0);
v___x_4240_ = lean_box(v_cfg_4229_);
v___f_4241_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4241_, 0, v_stx_4228_);
lean_closure_set(v___f_4241_, 1, v___x_4239_);
lean_closure_set(v___f_4241_, 2, v___x_4240_);
v___x_4242_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4241_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___boxed(lean_object* v_stx_4243_, lean_object* v_cfg_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
uint8_t v_cfg_boxed_4254_; lean_object* v_res_4255_; 
v_cfg_boxed_4254_ = lean_unbox(v_cfg_4244_);
v_res_4255_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(v_stx_4243_, v_cfg_boxed_4254_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec_ref(v_a_4247_);
lean_dec(v_a_4246_);
lean_dec_ref(v_a_4245_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(lean_object* v_ref_4256_, lean_object* v_msgData_4257_, uint8_t v_severity_4258_, uint8_t v_isSilent_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4256_, v_msgData_4257_, v_severity_4258_, v_isSilent_4259_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_4270_, lean_object* v_msgData_4271_, lean_object* v_severity_4272_, lean_object* v_isSilent_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
uint8_t v_severity_boxed_4283_; uint8_t v_isSilent_boxed_4284_; lean_object* v_res_4285_; 
v_severity_boxed_4283_ = lean_unbox(v_severity_4272_);
v_isSilent_boxed_4284_ = lean_unbox(v_isSilent_4273_);
v_res_4285_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(v_ref_4270_, v_msgData_4271_, v_severity_boxed_4283_, v_isSilent_boxed_4284_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v_ref_4270_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* v_stx_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; 
v___x_4296_ = lean_unsigned_to_nat(1u);
v___x_4297_ = l_Lean_Syntax_getArg(v_stx_4286_, v___x_4296_);
v___x_4298_ = 0;
v___x_4299_ = 1;
v___x_4300_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v___x_4297_, v___x_4298_, v___x_4299_, v_a_4287_, v_a_4293_, v_a_4294_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; uint8_t v___x_4302_; lean_object* v___x_4303_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4302_ = lean_unbox(v_a_4301_);
lean_dec(v_a_4301_);
v___x_4303_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(v_stx_4286_, v___x_4302_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
return v___x_4303_;
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec(v_stx_4286_);
v_a_4304_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4300_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4300_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* v_stx_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Elab_Tactic_evalConstructor(v_stx_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4336_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1));
v___x_4338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_4339_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 10, 0);
v___x_4340_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4336_, v___x_4337_, v___x_4338_, v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object* v_a_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_4370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6));
v___x_4371_ = l_Lean_addBuiltinDeclarationRanges(v___x_4369_, v___x_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* v_stx_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v___y_4385_; lean_object* v___x_4394_; uint8_t v_transparency_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; uint8_t v___x_4399_; 
v___x_4394_ = l_Lean_Meta_Context_config(v_a_4379_);
v_transparency_4395_ = lean_ctor_get_uint8(v___x_4394_, 9);
lean_dec_ref(v___x_4394_);
v___x_4396_ = lean_unsigned_to_nat(1u);
v___x_4397_ = l_Lean_Syntax_getArg(v_stx_4374_, v___x_4396_);
v___x_4398_ = 2;
v___x_4399_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4395_, v___x_4398_);
if (v___x_4399_ == 0)
{
lean_object* v_keyedConfig_4400_; uint8_t v_trackZetaDelta_4401_; lean_object* v_zetaDeltaSet_4402_; lean_object* v_lctx_4403_; lean_object* v_localInstances_4404_; lean_object* v_defEqCtx_x3f_4405_; lean_object* v_synthPendingDepth_4406_; lean_object* v_customCanUnfoldPredicate_x3f_4407_; uint8_t v_univApprox_4408_; uint8_t v_inTypeClassResolution_4409_; uint8_t v_cacheInferType_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_keyedConfig_4400_ = lean_ctor_get(v_a_4379_, 0);
v_trackZetaDelta_4401_ = lean_ctor_get_uint8(v_a_4379_, sizeof(void*)*7);
v_zetaDeltaSet_4402_ = lean_ctor_get(v_a_4379_, 1);
v_lctx_4403_ = lean_ctor_get(v_a_4379_, 2);
v_localInstances_4404_ = lean_ctor_get(v_a_4379_, 3);
v_defEqCtx_x3f_4405_ = lean_ctor_get(v_a_4379_, 4);
v_synthPendingDepth_4406_ = lean_ctor_get(v_a_4379_, 5);
v_customCanUnfoldPredicate_x3f_4407_ = lean_ctor_get(v_a_4379_, 6);
v_univApprox_4408_ = lean_ctor_get_uint8(v_a_4379_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4409_ = lean_ctor_get_uint8(v_a_4379_, sizeof(void*)*7 + 2);
v_cacheInferType_4410_ = lean_ctor_get_uint8(v_a_4379_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4400_);
v___x_4411_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4398_, v_keyedConfig_4400_);
lean_inc(v_customCanUnfoldPredicate_x3f_4407_);
lean_inc(v_synthPendingDepth_4406_);
lean_inc(v_defEqCtx_x3f_4405_);
lean_inc_ref(v_localInstances_4404_);
lean_inc_ref(v_lctx_4403_);
lean_inc(v_zetaDeltaSet_4402_);
v___x_4412_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v_zetaDeltaSet_4402_);
lean_ctor_set(v___x_4412_, 2, v_lctx_4403_);
lean_ctor_set(v___x_4412_, 3, v_localInstances_4404_);
lean_ctor_set(v___x_4412_, 4, v_defEqCtx_x3f_4405_);
lean_ctor_set(v___x_4412_, 5, v_synthPendingDepth_4406_);
lean_ctor_set(v___x_4412_, 6, v_customCanUnfoldPredicate_x3f_4407_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7, v_trackZetaDelta_4401_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7 + 1, v_univApprox_4408_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4409_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*7 + 3, v_cacheInferType_4410_);
v___x_4413_ = l_Lean_Elab_Tactic_evalTactic(v___x_4397_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v___x_4412_, v_a_4380_, v_a_4381_, v_a_4382_);
lean_dec_ref_known(v___x_4412_, 7);
v___y_4385_ = v___x_4413_;
goto v___jp_4384_;
}
else
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Elab_Tactic_evalTactic(v___x_4397_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
v___y_4385_ = v___x_4414_;
goto v___jp_4384_;
}
v___jp_4384_:
{
if (lean_obj_tag(v___y_4385_) == 0)
{
return v___y_4385_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___y_4385_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___y_4385_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___y_4385_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___y_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object* v_stx_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_Elab_Tactic_evalWithReducible(v_stx_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_stx_4415_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4439_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1));
v___x_4441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_4442_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
v___x_4443_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4439_, v___x_4440_, v___x_4441_, v___x_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6));
v___x_4474_ = l_Lean_addBuiltinDeclarationRanges(v___x_4472_, v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* v_stx_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v___y_4488_; lean_object* v___x_4497_; uint8_t v_transparency_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; uint8_t v___x_4501_; uint8_t v___x_4502_; 
v___x_4497_ = l_Lean_Meta_Context_config(v_a_4482_);
v_transparency_4498_ = lean_ctor_get_uint8(v___x_4497_, 9);
lean_dec_ref(v___x_4497_);
v___x_4499_ = lean_unsigned_to_nat(1u);
v___x_4500_ = l_Lean_Syntax_getArg(v_stx_4477_, v___x_4499_);
v___x_4501_ = 3;
v___x_4502_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4498_, v___x_4501_);
if (v___x_4502_ == 0)
{
lean_object* v_keyedConfig_4503_; uint8_t v_trackZetaDelta_4504_; lean_object* v_zetaDeltaSet_4505_; lean_object* v_lctx_4506_; lean_object* v_localInstances_4507_; lean_object* v_defEqCtx_x3f_4508_; lean_object* v_synthPendingDepth_4509_; lean_object* v_customCanUnfoldPredicate_x3f_4510_; uint8_t v_univApprox_4511_; uint8_t v_inTypeClassResolution_4512_; uint8_t v_cacheInferType_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v_keyedConfig_4503_ = lean_ctor_get(v_a_4482_, 0);
v_trackZetaDelta_4504_ = lean_ctor_get_uint8(v_a_4482_, sizeof(void*)*7);
v_zetaDeltaSet_4505_ = lean_ctor_get(v_a_4482_, 1);
v_lctx_4506_ = lean_ctor_get(v_a_4482_, 2);
v_localInstances_4507_ = lean_ctor_get(v_a_4482_, 3);
v_defEqCtx_x3f_4508_ = lean_ctor_get(v_a_4482_, 4);
v_synthPendingDepth_4509_ = lean_ctor_get(v_a_4482_, 5);
v_customCanUnfoldPredicate_x3f_4510_ = lean_ctor_get(v_a_4482_, 6);
v_univApprox_4511_ = lean_ctor_get_uint8(v_a_4482_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4512_ = lean_ctor_get_uint8(v_a_4482_, sizeof(void*)*7 + 2);
v_cacheInferType_4513_ = lean_ctor_get_uint8(v_a_4482_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4503_);
v___x_4514_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4501_, v_keyedConfig_4503_);
lean_inc(v_customCanUnfoldPredicate_x3f_4510_);
lean_inc(v_synthPendingDepth_4509_);
lean_inc(v_defEqCtx_x3f_4508_);
lean_inc_ref(v_localInstances_4507_);
lean_inc_ref(v_lctx_4506_);
lean_inc(v_zetaDeltaSet_4505_);
v___x_4515_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
lean_ctor_set(v___x_4515_, 1, v_zetaDeltaSet_4505_);
lean_ctor_set(v___x_4515_, 2, v_lctx_4506_);
lean_ctor_set(v___x_4515_, 3, v_localInstances_4507_);
lean_ctor_set(v___x_4515_, 4, v_defEqCtx_x3f_4508_);
lean_ctor_set(v___x_4515_, 5, v_synthPendingDepth_4509_);
lean_ctor_set(v___x_4515_, 6, v_customCanUnfoldPredicate_x3f_4510_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*7, v_trackZetaDelta_4504_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*7 + 1, v_univApprox_4511_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*7 + 3, v_cacheInferType_4513_);
v___x_4516_ = l_Lean_Elab_Tactic_evalTactic(v___x_4500_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v___x_4515_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec_ref_known(v___x_4515_, 7);
v___y_4488_ = v___x_4516_;
goto v___jp_4487_;
}
else
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_Elab_Tactic_evalTactic(v___x_4500_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
v___y_4488_ = v___x_4517_;
goto v___jp_4487_;
}
v___jp_4487_:
{
if (lean_obj_tag(v___y_4488_) == 0)
{
return v___y_4488_;
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
v_a_4489_ = lean_ctor_get(v___y_4488_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___y_4488_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___y_4488_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___y_4488_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object* v_stx_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(v_stx_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_stx_4518_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4542_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1));
v___x_4544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_4545_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
v___x_4546_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4542_, v___x_4543_, v___x_4544_, v___x_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_4576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6));
v___x_4577_ = l_Lean_addBuiltinDeclarationRanges(v___x_4575_, v___x_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object* v_a_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit(lean_object* v_stx_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v___y_4591_; lean_object* v___x_4600_; uint8_t v_transparency_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; uint8_t v___x_4605_; 
v___x_4600_ = l_Lean_Meta_Context_config(v_a_4585_);
v_transparency_4601_ = lean_ctor_get_uint8(v___x_4600_, 9);
lean_dec_ref(v___x_4600_);
v___x_4602_ = lean_unsigned_to_nat(1u);
v___x_4603_ = l_Lean_Syntax_getArg(v_stx_4580_, v___x_4602_);
v___x_4604_ = 5;
v___x_4605_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4601_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_object* v_keyedConfig_4606_; uint8_t v_trackZetaDelta_4607_; lean_object* v_zetaDeltaSet_4608_; lean_object* v_lctx_4609_; lean_object* v_localInstances_4610_; lean_object* v_defEqCtx_x3f_4611_; lean_object* v_synthPendingDepth_4612_; lean_object* v_customCanUnfoldPredicate_x3f_4613_; uint8_t v_univApprox_4614_; uint8_t v_inTypeClassResolution_4615_; uint8_t v_cacheInferType_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v_keyedConfig_4606_ = lean_ctor_get(v_a_4585_, 0);
v_trackZetaDelta_4607_ = lean_ctor_get_uint8(v_a_4585_, sizeof(void*)*7);
v_zetaDeltaSet_4608_ = lean_ctor_get(v_a_4585_, 1);
v_lctx_4609_ = lean_ctor_get(v_a_4585_, 2);
v_localInstances_4610_ = lean_ctor_get(v_a_4585_, 3);
v_defEqCtx_x3f_4611_ = lean_ctor_get(v_a_4585_, 4);
v_synthPendingDepth_4612_ = lean_ctor_get(v_a_4585_, 5);
v_customCanUnfoldPredicate_x3f_4613_ = lean_ctor_get(v_a_4585_, 6);
v_univApprox_4614_ = lean_ctor_get_uint8(v_a_4585_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4615_ = lean_ctor_get_uint8(v_a_4585_, sizeof(void*)*7 + 2);
v_cacheInferType_4616_ = lean_ctor_get_uint8(v_a_4585_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4606_);
v___x_4617_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4604_, v_keyedConfig_4606_);
lean_inc(v_customCanUnfoldPredicate_x3f_4613_);
lean_inc(v_synthPendingDepth_4612_);
lean_inc(v_defEqCtx_x3f_4611_);
lean_inc_ref(v_localInstances_4610_);
lean_inc_ref(v_lctx_4609_);
lean_inc(v_zetaDeltaSet_4608_);
v___x_4618_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
lean_ctor_set(v___x_4618_, 1, v_zetaDeltaSet_4608_);
lean_ctor_set(v___x_4618_, 2, v_lctx_4609_);
lean_ctor_set(v___x_4618_, 3, v_localInstances_4610_);
lean_ctor_set(v___x_4618_, 4, v_defEqCtx_x3f_4611_);
lean_ctor_set(v___x_4618_, 5, v_synthPendingDepth_4612_);
lean_ctor_set(v___x_4618_, 6, v_customCanUnfoldPredicate_x3f_4613_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*7, v_trackZetaDelta_4607_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*7 + 1, v_univApprox_4614_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4615_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*7 + 3, v_cacheInferType_4616_);
v___x_4619_ = l_Lean_Elab_Tactic_evalTactic(v___x_4603_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v___x_4618_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec_ref_known(v___x_4618_, 7);
v___y_4591_ = v___x_4619_;
goto v___jp_4590_;
}
else
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Lean_Elab_Tactic_evalTactic(v___x_4603_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
v___y_4591_ = v___x_4620_;
goto v___jp_4590_;
}
v___jp_4590_:
{
if (lean_obj_tag(v___y_4591_) == 0)
{
return v___y_4591_;
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
v_a_4592_ = lean_ctor_get(v___y_4591_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___y_4591_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___y_4591_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___y_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit___boxed(lean_object* v_stx_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Lean_Elab_Tactic_evalWithImplicit(v_stx_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_stx_4621_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1(){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4645_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1));
v___x_4647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3));
v___x_4648_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithImplicit___boxed), 10, 0);
v___x_4649_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4645_, v___x_4646_, v___x_4647_, v___x_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___boxed(lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* v_stx_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v___y_4663_; lean_object* v___x_4672_; uint8_t v_transparency_4673_; uint8_t v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; uint8_t v___x_4677_; 
v___x_4672_ = l_Lean_Meta_Context_config(v_a_4657_);
v_transparency_4673_ = lean_ctor_get_uint8(v___x_4672_, 9);
lean_dec_ref(v___x_4672_);
v___x_4674_ = 0;
v___x_4675_ = lean_unsigned_to_nat(1u);
v___x_4676_ = l_Lean_Syntax_getArg(v_stx_4652_, v___x_4675_);
v___x_4677_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4673_, v___x_4674_);
if (v___x_4677_ == 0)
{
lean_object* v_keyedConfig_4678_; uint8_t v_trackZetaDelta_4679_; lean_object* v_zetaDeltaSet_4680_; lean_object* v_lctx_4681_; lean_object* v_localInstances_4682_; lean_object* v_defEqCtx_x3f_4683_; lean_object* v_synthPendingDepth_4684_; lean_object* v_customCanUnfoldPredicate_x3f_4685_; uint8_t v_univApprox_4686_; uint8_t v_inTypeClassResolution_4687_; uint8_t v_cacheInferType_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v_keyedConfig_4678_ = lean_ctor_get(v_a_4657_, 0);
v_trackZetaDelta_4679_ = lean_ctor_get_uint8(v_a_4657_, sizeof(void*)*7);
v_zetaDeltaSet_4680_ = lean_ctor_get(v_a_4657_, 1);
v_lctx_4681_ = lean_ctor_get(v_a_4657_, 2);
v_localInstances_4682_ = lean_ctor_get(v_a_4657_, 3);
v_defEqCtx_x3f_4683_ = lean_ctor_get(v_a_4657_, 4);
v_synthPendingDepth_4684_ = lean_ctor_get(v_a_4657_, 5);
v_customCanUnfoldPredicate_x3f_4685_ = lean_ctor_get(v_a_4657_, 6);
v_univApprox_4686_ = lean_ctor_get_uint8(v_a_4657_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4687_ = lean_ctor_get_uint8(v_a_4657_, sizeof(void*)*7 + 2);
v_cacheInferType_4688_ = lean_ctor_get_uint8(v_a_4657_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4678_);
v___x_4689_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4674_, v_keyedConfig_4678_);
lean_inc(v_customCanUnfoldPredicate_x3f_4685_);
lean_inc(v_synthPendingDepth_4684_);
lean_inc(v_defEqCtx_x3f_4683_);
lean_inc_ref(v_localInstances_4682_);
lean_inc_ref(v_lctx_4681_);
lean_inc(v_zetaDeltaSet_4680_);
v___x_4690_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
lean_ctor_set(v___x_4690_, 1, v_zetaDeltaSet_4680_);
lean_ctor_set(v___x_4690_, 2, v_lctx_4681_);
lean_ctor_set(v___x_4690_, 3, v_localInstances_4682_);
lean_ctor_set(v___x_4690_, 4, v_defEqCtx_x3f_4683_);
lean_ctor_set(v___x_4690_, 5, v_synthPendingDepth_4684_);
lean_ctor_set(v___x_4690_, 6, v_customCanUnfoldPredicate_x3f_4685_);
lean_ctor_set_uint8(v___x_4690_, sizeof(void*)*7, v_trackZetaDelta_4679_);
lean_ctor_set_uint8(v___x_4690_, sizeof(void*)*7 + 1, v_univApprox_4686_);
lean_ctor_set_uint8(v___x_4690_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4687_);
lean_ctor_set_uint8(v___x_4690_, sizeof(void*)*7 + 3, v_cacheInferType_4688_);
v___x_4691_ = l_Lean_Elab_Tactic_evalTactic(v___x_4676_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v___x_4690_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec_ref_known(v___x_4690_, 7);
v___y_4663_ = v___x_4691_;
goto v___jp_4662_;
}
else
{
lean_object* v___x_4692_; 
v___x_4692_ = l_Lean_Elab_Tactic_evalTactic(v___x_4676_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
v___y_4663_ = v___x_4692_;
goto v___jp_4662_;
}
v___jp_4662_:
{
if (lean_obj_tag(v___y_4663_) == 0)
{
return v___y_4663_;
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
v_a_4664_ = lean_ctor_get(v___y_4663_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___y_4663_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___y_4663_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___y_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object* v_stx_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Lean_Elab_Tactic_evalWithUnfoldingAll(v_stx_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_stx_4693_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4717_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4718_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1));
v___x_4719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_4720_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
v___x_4721_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4717_, v___x_4718_, v___x_4719_, v___x_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object* v_a_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6));
v___x_4752_ = l_Lean_addBuiltinDeclarationRanges(v___x_4750_, v___x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object* v_stx_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_){
_start:
{
lean_object* v___y_4766_; lean_object* v___x_4775_; uint8_t v_transparency_4776_; uint8_t v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; 
v___x_4775_ = l_Lean_Meta_Context_config(v_a_4760_);
v_transparency_4776_ = lean_ctor_get_uint8(v___x_4775_, 9);
lean_dec_ref(v___x_4775_);
v___x_4777_ = 4;
v___x_4778_ = lean_unsigned_to_nat(1u);
v___x_4779_ = l_Lean_Syntax_getArg(v_stx_4755_, v___x_4778_);
v___x_4780_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4776_, v___x_4777_);
if (v___x_4780_ == 0)
{
lean_object* v_keyedConfig_4781_; uint8_t v_trackZetaDelta_4782_; lean_object* v_zetaDeltaSet_4783_; lean_object* v_lctx_4784_; lean_object* v_localInstances_4785_; lean_object* v_defEqCtx_x3f_4786_; lean_object* v_synthPendingDepth_4787_; lean_object* v_customCanUnfoldPredicate_x3f_4788_; uint8_t v_univApprox_4789_; uint8_t v_inTypeClassResolution_4790_; uint8_t v_cacheInferType_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v_keyedConfig_4781_ = lean_ctor_get(v_a_4760_, 0);
v_trackZetaDelta_4782_ = lean_ctor_get_uint8(v_a_4760_, sizeof(void*)*7);
v_zetaDeltaSet_4783_ = lean_ctor_get(v_a_4760_, 1);
v_lctx_4784_ = lean_ctor_get(v_a_4760_, 2);
v_localInstances_4785_ = lean_ctor_get(v_a_4760_, 3);
v_defEqCtx_x3f_4786_ = lean_ctor_get(v_a_4760_, 4);
v_synthPendingDepth_4787_ = lean_ctor_get(v_a_4760_, 5);
v_customCanUnfoldPredicate_x3f_4788_ = lean_ctor_get(v_a_4760_, 6);
v_univApprox_4789_ = lean_ctor_get_uint8(v_a_4760_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4790_ = lean_ctor_get_uint8(v_a_4760_, sizeof(void*)*7 + 2);
v_cacheInferType_4791_ = lean_ctor_get_uint8(v_a_4760_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4781_);
v___x_4792_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4777_, v_keyedConfig_4781_);
lean_inc(v_customCanUnfoldPredicate_x3f_4788_);
lean_inc(v_synthPendingDepth_4787_);
lean_inc(v_defEqCtx_x3f_4786_);
lean_inc_ref(v_localInstances_4785_);
lean_inc_ref(v_lctx_4784_);
lean_inc(v_zetaDeltaSet_4783_);
v___x_4793_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
lean_ctor_set(v___x_4793_, 1, v_zetaDeltaSet_4783_);
lean_ctor_set(v___x_4793_, 2, v_lctx_4784_);
lean_ctor_set(v___x_4793_, 3, v_localInstances_4785_);
lean_ctor_set(v___x_4793_, 4, v_defEqCtx_x3f_4786_);
lean_ctor_set(v___x_4793_, 5, v_synthPendingDepth_4787_);
lean_ctor_set(v___x_4793_, 6, v_customCanUnfoldPredicate_x3f_4788_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*7, v_trackZetaDelta_4782_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*7 + 1, v_univApprox_4789_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4790_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*7 + 3, v_cacheInferType_4791_);
v___x_4794_ = l_Lean_Elab_Tactic_evalTactic(v___x_4779_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v___x_4793_, v_a_4761_, v_a_4762_, v_a_4763_);
lean_dec_ref_known(v___x_4793_, 7);
v___y_4766_ = v___x_4794_;
goto v___jp_4765_;
}
else
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Lean_Elab_Tactic_evalTactic(v___x_4779_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
v___y_4766_ = v___x_4795_;
goto v___jp_4765_;
}
v___jp_4765_:
{
if (lean_obj_tag(v___y_4766_) == 0)
{
return v___y_4766_;
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
v_a_4767_ = lean_ctor_get(v___y_4766_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___y_4766_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___y_4766_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___y_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object* v_stx_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Lean_Elab_Tactic_evalWithUnfoldingNone(v_stx_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_stx_4796_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1(){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4820_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1));
v___x_4822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3));
v___x_4823_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed), 10, 0);
v___x_4824_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4820_, v___x_4821_, v___x_4822_, v___x_4823_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object* v_stx_4830_, lean_object* v___x_4831_, uint8_t v___x_4832_, lean_object* v_userName_x3f_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_Elab_Tactic_elabTerm(v_stx_4830_, v___x_4831_, v___x_4832_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4930_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4846_ = v___x_4843_;
v_isShared_4847_ = v_isSharedCheck_4930_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4843_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4930_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
if (lean_obj_tag(v_a_4844_) == 1)
{
lean_object* v_fvarId_4848_; lean_object* v___x_4850_; 
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v_userName_x3f_4833_);
v_fvarId_4848_ = lean_ctor_get(v_a_4844_, 0);
lean_inc(v_fvarId_4848_);
lean_dec_ref_known(v_a_4844_, 1);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 0, v_fvarId_4848_);
v___x_4850_ = v___x_4846_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_fvarId_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
else
{
lean_object* v___x_4852_; 
lean_del_object(v___x_4846_);
lean_inc(v___y_4841_);
lean_inc_ref(v___y_4840_);
lean_inc(v___y_4839_);
lean_inc_ref(v___y_4838_);
lean_inc(v_a_4844_);
v___x_4852_ = lean_infer_type(v_a_4844_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v_userName_4855_; uint8_t v_preserveBinderNames_4856_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
if (lean_obj_tag(v_userName_x3f_4833_) == 0)
{
lean_object* v___x_4919_; 
v___x_4919_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1));
v_userName_4855_ = v___x_4919_;
v_preserveBinderNames_4856_ = v___x_4832_;
v___y_4857_ = v___y_4835_;
v___y_4858_ = v___y_4838_;
v___y_4859_ = v___y_4839_;
v___y_4860_ = v___y_4840_;
v___y_4861_ = v___y_4841_;
goto v___jp_4854_;
}
else
{
lean_object* v_val_4920_; uint8_t v___x_4921_; 
v_val_4920_ = lean_ctor_get(v_userName_x3f_4833_, 0);
lean_inc(v_val_4920_);
lean_dec_ref_known(v_userName_x3f_4833_, 1);
v___x_4921_ = 1;
v_userName_4855_ = v_val_4920_;
v_preserveBinderNames_4856_ = v___x_4921_;
v___y_4857_ = v___y_4835_;
v___y_4858_ = v___y_4838_;
v___y_4859_ = v___y_4839_;
v___y_4860_ = v___y_4840_;
v___y_4861_ = v___y_4841_;
goto v___jp_4854_;
}
v___jp_4854_:
{
lean_object* v___x_4862_; 
v___x_4862_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v___x_4864_ = l_Lean_MVarId_assert(v_a_4863_, v_userName_4855_, v_a_4853_, v_a_4844_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = l_Lean_Meta_intro1Core(v_a_4865_, v_preserveBinderNames_4856_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v_fst_4868_; lean_object* v_snd_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4894_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v_fst_4868_ = lean_ctor_get(v_a_4867_, 0);
v_snd_4869_ = lean_ctor_get(v_a_4867_, 1);
v_isSharedCheck_4894_ = !lean_is_exclusive(v_a_4867_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4871_ = v_a_4867_;
v_isShared_4872_ = v_isSharedCheck_4894_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_snd_4869_);
lean_inc(v_fst_4868_);
lean_dec(v_a_4867_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4894_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4873_ = lean_box(0);
if (v_isShared_4872_ == 0)
{
lean_ctor_set_tag(v___x_4871_, 1);
lean_ctor_set(v___x_4871_, 1, v___x_4873_);
lean_ctor_set(v___x_4871_, 0, v_snd_4869_);
v___x_4875_ = v___x_4871_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_snd_4869_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
lean_object* v___x_4876_; 
v___x_4876_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4875_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4883_ == 0)
{
lean_object* v_unused_4884_; 
v_unused_4884_ = lean_ctor_get(v___x_4876_, 0);
lean_dec(v_unused_4884_);
v___x_4878_ = v___x_4876_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_dec(v___x_4876_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v_fst_4868_);
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_fst_4868_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec(v_fst_4868_);
v_a_4885_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4876_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4876_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
v_a_4895_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4866_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4866_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
v_a_4903_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4864_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4864_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v_userName_4855_);
lean_dec(v_a_4853_);
lean_dec(v_a_4844_);
v_a_4911_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4862_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4862_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_dec(v_a_4844_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v_userName_x3f_4833_);
v_a_4922_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4852_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4852_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
}
else
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4938_; 
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v_userName_x3f_4833_);
v_a_4931_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4933_ = v___x_4843_;
v_isShared_4934_ = v_isSharedCheck_4938_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v___x_4843_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4938_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4936_; 
if (v_isShared_4934_ == 0)
{
v___x_4936_ = v___x_4933_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object* v_stx_4939_, lean_object* v___x_4940_, lean_object* v___x_4941_, lean_object* v_userName_x3f_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
uint8_t v___x_1502__boxed_4952_; lean_object* v_res_4953_; 
v___x_1502__boxed_4952_ = lean_unbox(v___x_4941_);
v_res_4953_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0(v_stx_4939_, v___x_4940_, v___x_1502__boxed_4952_, v_userName_x3f_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* v_stx_4954_, lean_object* v_userName_x3f_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___x_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; lean_object* v___f_4968_; lean_object* v___x_4969_; 
v___x_4965_ = lean_box(0);
v___x_4966_ = 0;
v___x_4967_ = lean_box(v___x_4966_);
v___f_4968_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4968_, 0, v_stx_4954_);
lean_closure_set(v___f_4968_, 1, v___x_4965_);
lean_closure_set(v___f_4968_, 2, v___x_4967_);
lean_closure_set(v___f_4968_, 3, v_userName_x3f_4955_);
v___x_4969_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4968_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object* v_stx_4970_, lean_object* v_userName_x3f_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l_Lean_Elab_Tactic_elabAsFVar(v_stx_4970_, v_userName_x3f_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object* v_k_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v___x_4992_; 
lean_inc(v___y_4986_);
lean_inc_ref(v___y_4985_);
lean_inc(v___y_4984_);
lean_inc_ref(v___y_4983_);
v___x_4992_ = lean_apply_9(v_k_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, lean_box(0));
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object* v_k_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(v_k_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object* v_k_5004_, uint8_t v_allowLevelAssignments_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v___f_5015_; lean_object* v___x_5016_; 
lean_inc(v___y_5009_);
lean_inc_ref(v___y_5008_);
lean_inc(v___y_5007_);
lean_inc_ref(v___y_5006_);
v___f_5015_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5015_, 0, v_k_5004_);
lean_closure_set(v___f_5015_, 1, v___y_5006_);
lean_closure_set(v___f_5015_, 2, v___y_5007_);
lean_closure_set(v___f_5015_, 3, v___y_5008_);
lean_closure_set(v___f_5015_, 4, v___y_5009_);
v___x_5016_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_5005_, v___f_5015_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
if (lean_obj_tag(v___x_5016_) == 0)
{
return v___x_5016_;
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_5016_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5016_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object* v_k_5025_, lean_object* v_allowLevelAssignments_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5036_; lean_object* v_res_5037_; 
v_allowLevelAssignments_boxed_5036_ = lean_unbox(v_allowLevelAssignments_5026_);
v_res_5037_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_5025_, v_allowLevelAssignments_boxed_5036_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object* v_00_u03b1_5038_, lean_object* v_k_5039_, uint8_t v_allowLevelAssignments_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_5039_, v_allowLevelAssignments_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object* v_00_u03b1_5051_, lean_object* v_k_5052_, lean_object* v_allowLevelAssignments_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5063_; lean_object* v_res_5064_; 
v_allowLevelAssignments_boxed_5063_ = lean_unbox(v_allowLevelAssignments_5053_);
v_res_5064_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(v_00_u03b1_5051_, v_k_5052_, v_allowLevelAssignments_boxed_5063_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object* v_a_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v_a_x3f_5073_){
_start:
{
uint8_t v___x_5075_; lean_object* v___x_5076_; 
v___x_5075_ = 0;
v___x_5076_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_5065_, v___x_5075_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object* v_a_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v_a_x3f_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v_a_x3f_5085_);
lean_dec(v_a_x3f_5085_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object* v_x_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_5090_, v___y_5092_, v___y_5094_, v___y_5096_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v_r_5100_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
lean_inc(v___y_5096_);
lean_inc_ref(v___y_5095_);
lean_inc(v___y_5094_);
lean_inc_ref(v___y_5093_);
lean_inc(v___y_5092_);
lean_inc_ref(v___y_5091_);
lean_inc(v___y_5090_);
lean_inc_ref(v___y_5089_);
v_r_5100_ = lean_apply_9(v_x_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, lean_box(0));
if (lean_obj_tag(v_r_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5125_; 
v_a_5101_ = lean_ctor_get(v_r_5100_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v_r_5100_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5103_ = v_r_5100_;
v_isShared_5104_ = v_isSharedCheck_5125_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v_r_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5125_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
lean_inc(v_a_5101_);
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 1);
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5099_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___x_5106_);
lean_dec_ref(v___x_5106_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; 
v_unused_5115_ = lean_ctor_get(v___x_5107_, 0);
lean_dec(v_unused_5115_);
v___x_5109_ = v___x_5107_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_dec(v___x_5107_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set(v___x_5109_, 0, v_a_5101_);
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5101_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec(v_a_5101_);
v_a_5116_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5107_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5107_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_a_5126_ = lean_ctor_get(v_r_5100_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v_r_5100_, 1);
v___x_5127_ = lean_box(0);
v___x_5128_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5099_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___x_5127_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5135_; 
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5135_ == 0)
{
lean_object* v_unused_5136_; 
v_unused_5136_ = lean_ctor_get(v___x_5128_, 0);
lean_dec(v_unused_5136_);
v___x_5130_ = v___x_5128_;
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
else
{
lean_dec(v___x_5128_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5133_; 
if (v_isShared_5131_ == 0)
{
lean_ctor_set_tag(v___x_5130_, 1);
lean_ctor_set(v___x_5130_, 0, v_a_5126_);
v___x_5133_ = v___x_5130_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5126_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_dec(v_a_5126_);
v_a_5137_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5128_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5128_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec_ref(v_x_5088_);
v_a_5145_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5098_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5098_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object* v_x_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
lean_dec(v___y_5157_);
lean_dec_ref(v___y_5156_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object* v_00_u03b1_5164_, lean_object* v_x_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v___x_5175_; 
v___x_5175_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
return v___x_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object* v_00_u03b1_5176_, lean_object* v_x_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(v_00_u03b1_5176_, v_x_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object* v_a_5188_, lean_object* v_as_5189_, lean_object* v_i_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v_zero_5196_; uint8_t v_isZero_5197_; 
v_zero_5196_ = lean_unsigned_to_nat(0u);
v_isZero_5197_ = lean_nat_dec_eq(v_i_5190_, v_zero_5196_);
if (v_isZero_5197_ == 1)
{
lean_object* v___x_5198_; lean_object* v___x_5199_; 
lean_dec(v_i_5190_);
lean_dec_ref(v_a_5188_);
v___x_5198_ = lean_box(0);
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
return v___x_5199_;
}
else
{
lean_object* v_one_5200_; lean_object* v_n_5201_; lean_object* v___x_5202_; 
v_one_5200_ = lean_unsigned_to_nat(1u);
v_n_5201_ = lean_nat_sub(v_i_5190_, v_one_5200_);
lean_dec(v_i_5190_);
v___x_5202_ = lean_array_fget(v_as_5189_, v_n_5201_);
if (lean_obj_tag(v___x_5202_) == 0)
{
v_i_5190_ = v_n_5201_;
goto _start;
}
else
{
lean_object* v_val_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5234_; 
v_val_5204_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5206_ = v___x_5202_;
v_isShared_5207_ = v_isSharedCheck_5234_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_val_5204_);
lean_dec(v___x_5202_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5234_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5208_ = l_Lean_LocalDecl_type(v_val_5204_);
lean_inc_ref(v_a_5188_);
v___x_5209_ = l_Lean_Meta_isExprDefEq(v_a_5188_, v___x_5208_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5225_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5212_ = v___x_5209_;
v_isShared_5213_ = v_isSharedCheck_5225_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5225_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
uint8_t v___x_5214_; 
v___x_5214_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5204_);
if (v___x_5214_ == 0)
{
uint8_t v___x_5215_; 
v___x_5215_ = lean_unbox(v_a_5210_);
lean_dec(v_a_5210_);
if (v___x_5215_ == 0)
{
lean_del_object(v___x_5212_);
lean_del_object(v___x_5206_);
lean_dec(v_val_5204_);
v_i_5190_ = v_n_5201_;
goto _start;
}
else
{
lean_object* v___x_5217_; lean_object* v___x_5219_; 
lean_dec(v_n_5201_);
lean_dec_ref(v_a_5188_);
v___x_5217_ = l_Lean_LocalDecl_fvarId(v_val_5204_);
lean_dec(v_val_5204_);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v___x_5217_);
v___x_5219_ = v___x_5206_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5217_);
v___x_5219_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
lean_object* v___x_5221_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5219_);
v___x_5221_ = v___x_5212_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
else
{
lean_del_object(v___x_5212_);
lean_dec(v_a_5210_);
lean_del_object(v___x_5206_);
lean_dec(v_val_5204_);
v_i_5190_ = v_n_5201_;
goto _start;
}
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_del_object(v___x_5206_);
lean_dec(v_val_5204_);
lean_dec(v_n_5201_);
lean_dec_ref(v_a_5188_);
v_a_5226_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5209_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5209_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_a_5235_, lean_object* v_as_5236_, lean_object* v_i_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5235_, v_as_5236_, v_i_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec_ref(v_as_5236_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_5244_, lean_object* v_as_5245_, lean_object* v_i_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_zero_5256_; uint8_t v_isZero_5257_; 
v_zero_5256_ = lean_unsigned_to_nat(0u);
v_isZero_5257_ = lean_nat_dec_eq(v_i_5246_, v_zero_5256_);
if (v_isZero_5257_ == 1)
{
lean_object* v___x_5258_; lean_object* v___x_5259_; 
lean_dec(v_i_5246_);
lean_dec_ref(v_a_5244_);
v___x_5258_ = lean_box(0);
v___x_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5259_, 0, v___x_5258_);
return v___x_5259_;
}
else
{
lean_object* v_one_5260_; lean_object* v_n_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; 
v_one_5260_ = lean_unsigned_to_nat(1u);
v_n_5261_ = lean_nat_sub(v_i_5246_, v_one_5260_);
lean_dec(v_i_5246_);
v___x_5262_ = lean_array_fget_borrowed(v_as_5245_, v_n_5261_);
lean_inc_ref(v_a_5244_);
v___x_5263_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5244_, v___x_5262_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
if (lean_obj_tag(v___x_5263_) == 0)
{
lean_object* v_a_5264_; 
v_a_5264_ = lean_ctor_get(v___x_5263_, 0);
if (lean_obj_tag(v_a_5264_) == 0)
{
lean_dec_ref_known(v___x_5263_, 1);
v_i_5246_ = v_n_5261_;
goto _start;
}
else
{
lean_dec(v_n_5261_);
lean_dec_ref(v_a_5244_);
return v___x_5263_;
}
}
else
{
lean_dec(v_n_5261_);
lean_dec_ref(v_a_5244_);
return v___x_5263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object* v_a_5266_, lean_object* v_x_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
if (lean_obj_tag(v_x_5267_) == 0)
{
lean_object* v_cs_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v_cs_5277_ = lean_ctor_get(v_x_5267_, 0);
v___x_5278_ = lean_array_get_size(v_cs_5277_);
v___x_5279_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5266_, v_cs_5277_, v___x_5278_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
return v___x_5279_;
}
else
{
lean_object* v_vs_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v_vs_5280_ = lean_ctor_get(v_x_5267_, 0);
v___x_5281_ = lean_array_get_size(v_vs_5280_);
v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5266_, v_vs_5280_, v___x_5281_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
return v___x_5282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object* v_a_5283_, lean_object* v_x_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5283_, v_x_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec_ref(v_x_5284_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_5295_, lean_object* v_as_5296_, lean_object* v_i_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5295_, v_as_5296_, v_i_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec_ref(v_as_5296_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object* v_a_5308_, lean_object* v_t_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
lean_object* v_root_5319_; lean_object* v_tail_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v_root_5319_ = lean_ctor_get(v_t_5309_, 0);
v_tail_5320_ = lean_ctor_get(v_t_5309_, 1);
v___x_5321_ = lean_array_get_size(v_tail_5320_);
lean_inc_ref(v_a_5308_);
v___x_5322_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5308_, v_tail_5320_, v___x_5321_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
if (lean_obj_tag(v_a_5323_) == 0)
{
lean_object* v___x_5324_; 
lean_dec_ref_known(v___x_5322_, 1);
v___x_5324_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5308_, v_root_5319_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
return v___x_5324_;
}
else
{
lean_dec_ref(v_a_5308_);
return v___x_5322_;
}
}
else
{
lean_dec_ref(v_a_5308_);
return v___x_5322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object* v_a_5325_, lean_object* v_t_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_5325_, v_t_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec_ref(v_t_5326_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object* v_a_5337_, lean_object* v_lctx_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_decls_5348_; lean_object* v___x_5349_; 
v_decls_5348_ = lean_ctor_get(v_lctx_5338_, 1);
v___x_5349_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_5337_, v_decls_5348_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object* v_a_5350_, lean_object* v_lctx_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_5350_, v_lctx_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec_ref(v_lctx_5351_);
return v_res_5361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5363_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0));
v___x_5364_ = l_Lean_stringToMessageData(v___x_5363_);
return v___x_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object* v___x_5365_, lean_object* v___x_5366_, uint8_t v___x_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v___x_5377_; 
v___x_5377_ = l_Lean_Elab_Tactic_elabTerm(v___x_5365_, v___x_5366_, v___x_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
if (lean_obj_tag(v___x_5377_) == 0)
{
lean_object* v_a_5378_; lean_object* v_lctx_5379_; lean_object* v___x_5380_; 
v_a_5378_ = lean_ctor_get(v___x_5377_, 0);
lean_inc_n(v_a_5378_, 2);
lean_dec_ref_known(v___x_5377_, 1);
v_lctx_5379_ = lean_ctor_get(v___y_5372_, 2);
v___x_5380_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_5378_, v_lctx_5379_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
if (lean_obj_tag(v___x_5380_) == 0)
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5393_; 
v_a_5381_ = lean_ctor_get(v___x_5380_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5380_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5383_ = v___x_5380_;
v_isShared_5384_ = v_isSharedCheck_5393_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5380_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5393_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
if (lean_obj_tag(v_a_5381_) == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
lean_del_object(v___x_5383_);
v___x_5385_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRename___lam__0___closed__1, &l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1);
v___x_5386_ = l_Lean_indentExpr(v_a_5378_);
v___x_5387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5385_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_5387_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
return v___x_5388_;
}
else
{
lean_object* v_val_5389_; lean_object* v___x_5391_; 
lean_dec(v_a_5378_);
v_val_5389_ = lean_ctor_get(v_a_5381_, 0);
lean_inc(v_val_5389_);
lean_dec_ref_known(v_a_5381_, 1);
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 0, v_val_5389_);
v___x_5391_ = v___x_5383_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_val_5389_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_dec(v_a_5378_);
v_a_5394_ = lean_ctor_get(v___x_5380_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5380_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5380_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5380_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
v_a_5402_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5377_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5377_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object* v___x_5410_, lean_object* v___x_5411_, lean_object* v___x_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
uint8_t v___x_6712__boxed_5422_; lean_object* v_res_5423_; 
v___x_6712__boxed_5422_ = lean_unbox(v___x_5412_);
v_res_5423_ = l_Lean_Elab_Tactic_evalRename___lam__0(v___x_5410_, v___x_5411_, v___x_6712__boxed_5422_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object* v___x_5424_, lean_object* v_h_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v___x_5435_; 
v___x_5435_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v___x_5424_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref_known(v___x_5435_, 1);
v___x_5437_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5427_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_object* v_a_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc(v_a_5438_);
lean_dec_ref_known(v___x_5437_, 1);
v___x_5439_ = l_Lean_TSyntax_getId(v_h_5425_);
v___x_5440_ = l_Lean_MVarId_rename(v_a_5438_, v_a_5436_, v___x_5439_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v___x_5440_, 1);
v___x_5442_ = lean_box(0);
v___x_5443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5443_, 0, v_a_5441_);
lean_ctor_set(v___x_5443_, 1, v___x_5442_);
v___x_5444_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5443_, v___y_5427_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
return v___x_5444_;
}
else
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
v_a_5445_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5440_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5440_);
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
lean_object* v_a_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5460_; 
lean_dec(v_a_5436_);
v_a_5453_ = lean_ctor_get(v___x_5437_, 0);
v_isSharedCheck_5460_ = !lean_is_exclusive(v___x_5437_);
if (v_isSharedCheck_5460_ == 0)
{
v___x_5455_ = v___x_5437_;
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_a_5453_);
lean_dec(v___x_5437_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v___x_5458_; 
if (v_isShared_5456_ == 0)
{
v___x_5458_ = v___x_5455_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
else
{
lean_object* v_a_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5468_; 
v_a_5461_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5463_ = v___x_5435_;
v_isShared_5464_ = v_isSharedCheck_5468_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_a_5461_);
lean_dec(v___x_5435_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5468_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5466_; 
if (v_isShared_5464_ == 0)
{
v___x_5466_ = v___x_5463_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5461_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object* v___x_5469_, lean_object* v_h_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_){
_start:
{
lean_object* v_res_5480_; 
v_res_5480_ = l_Lean_Elab_Tactic_evalRename___lam__1(v___x_5469_, v_h_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_);
lean_dec(v___y_5478_);
lean_dec_ref(v___y_5477_);
lean_dec(v___y_5476_);
lean_dec_ref(v___y_5475_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
lean_dec(v_h_5470_);
return v_res_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* v_stx_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_){
_start:
{
lean_object* v___x_5500_; uint8_t v___x_5501_; 
v___x_5500_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
lean_inc(v_stx_5490_);
v___x_5501_ = l_Lean_Syntax_isOfKind(v_stx_5490_, v___x_5500_);
if (v___x_5501_ == 0)
{
lean_object* v___x_5502_; 
lean_dec(v_stx_5490_);
v___x_5502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_5502_;
}
else
{
lean_object* v___x_5503_; lean_object* v_h_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; 
v___x_5503_ = lean_unsigned_to_nat(3u);
v_h_5504_ = l_Lean_Syntax_getArg(v_stx_5490_, v___x_5503_);
v___x_5505_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__3));
lean_inc(v_h_5504_);
v___x_5506_ = l_Lean_Syntax_isOfKind(v_h_5504_, v___x_5505_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; 
lean_dec(v_h_5504_);
lean_dec(v_stx_5490_);
v___x_5507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_5507_;
}
else
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___f_5512_; lean_object* v___x_5513_; uint8_t v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___f_5517_; lean_object* v___x_5518_; 
v___x_5508_ = lean_unsigned_to_nat(1u);
v___x_5509_ = l_Lean_Syntax_getArg(v_stx_5490_, v___x_5508_);
lean_dec(v_stx_5490_);
v___x_5510_ = lean_box(0);
v___x_5511_ = lean_box(v___x_5506_);
v___f_5512_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__0___boxed), 12, 3);
lean_closure_set(v___f_5512_, 0, v___x_5509_);
lean_closure_set(v___f_5512_, 1, v___x_5510_);
lean_closure_set(v___f_5512_, 2, v___x_5511_);
v___x_5513_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_5513_, 0, lean_box(0));
lean_closure_set(v___x_5513_, 1, v___f_5512_);
v___x_5514_ = 0;
v___x_5515_ = lean_box(v___x_5514_);
v___x_5516_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed), 12, 3);
lean_closure_set(v___x_5516_, 0, lean_box(0));
lean_closure_set(v___x_5516_, 1, v___x_5513_);
lean_closure_set(v___x_5516_, 2, v___x_5515_);
v___f_5517_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__1___boxed), 11, 2);
lean_closure_set(v___f_5517_, 0, v___x_5516_);
lean_closure_set(v___f_5517_, 1, v_h_5504_);
v___x_5518_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5517_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_);
return v___x_5518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object* v_stx_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_){
_start:
{
lean_object* v_res_5529_; 
v_res_5529_ = l_Lean_Elab_Tactic_evalRename(v_stx_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_);
lean_dec(v_a_5527_);
lean_dec_ref(v_a_5526_);
lean_dec(v_a_5525_);
lean_dec_ref(v_a_5524_);
lean_dec(v_a_5523_);
lean_dec_ref(v_a_5522_);
lean_dec(v_a_5521_);
lean_dec_ref(v_a_5520_);
return v_res_5529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object* v_a_5530_, lean_object* v_as_5531_, lean_object* v_i_5532_, lean_object* v_a_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v___x_5543_; 
v___x_5543_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5530_, v_as_5531_, v_i_5532_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_);
return v___x_5543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object* v_a_5544_, lean_object* v_as_5545_, lean_object* v_i_5546_, lean_object* v_a_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_){
_start:
{
lean_object* v_res_5557_; 
v_res_5557_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(v_a_5544_, v_as_5545_, v_i_5546_, v_a_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_);
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec_ref(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v___y_5548_);
lean_dec_ref(v_as_5545_);
return v_res_5557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object* v_a_5558_, lean_object* v_as_5559_, lean_object* v_i_5560_, lean_object* v_a_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v___x_5571_; 
v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5558_, v_as_5559_, v_i_5560_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
return v___x_5571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_a_5572_, lean_object* v_as_5573_, lean_object* v_i_5574_, lean_object* v_a_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v_res_5585_; 
v_res_5585_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(v_a_5572_, v_as_5573_, v_i_5574_, v_a_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
lean_dec(v___y_5583_);
lean_dec_ref(v___y_5582_);
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec_ref(v_as_5573_);
return v_res_5585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(){
_start:
{
lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; 
v___x_5593_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5594_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
v___x_5595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_5596_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___boxed), 10, 0);
v___x_5597_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5593_, v___x_5594_, v___x_5595_, v___x_5596_);
return v___x_5597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object* v_a_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(){
_start:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_5627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6));
v___x_5628_ = l_Lean_addBuiltinDeclarationRanges(v___x_5626_, v___x_5627_);
return v___x_5628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object* v_a_5629_){
_start:
{
lean_object* v_res_5630_; 
v_res_5630_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
return v_res_5630_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_ElabTerm(builtin);
}
#ifdef __cplusplus
}
#endif
