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
lean_object* v_declName_x3f_149_; lean_object* v_macroStack_150_; uint8_t v_mayPostpone_151_; uint8_t v_errToSorry_152_; lean_object* v_autoBoundImplicitContext_153_; lean_object* v_autoBoundImplicitForbidden_154_; lean_object* v_sectionVars_155_; lean_object* v_sectionFVars_156_; uint8_t v_implicitLambda_157_; uint8_t v_heedElabAsElim_158_; uint8_t v_isNoncomputableSection_159_; uint8_t v_isMetaSection_160_; uint8_t v_ignoreTCFailures_161_; uint8_t v_inPattern_162_; lean_object* v_tacSnap_x3f_163_; uint8_t v_saveRecAppSyntax_164_; uint8_t v_holesAsSyntheticOpaque_165_; lean_object* v_fixedTermElabs_166_; lean_object* v___y_168_; uint8_t v___y_172_; 
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
v_fixedTermElabs_166_ = lean_ctor_get(v___y_142_, 7);
if (lean_obj_tag(v_tacSnap_x3f_163_) == 0)
{
v___y_168_ = v_tacSnap_x3f_163_;
goto v___jp_167_;
}
else
{
lean_object* v_val_174_; lean_object* v_old_x3f_175_; lean_object* v___x_176_; lean_object* v___f_177_; 
v_val_174_ = lean_ctor_get(v_tacSnap_x3f_163_, 0);
v_old_x3f_175_ = lean_ctor_get(v_val_174_, 0);
v___x_176_ = lean_box(v_cond_138_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_177_, 0, v___x_176_);
if (lean_obj_tag(v_old_x3f_175_) == 1)
{
if (v_cond_138_ == 0)
{
lean_dec_ref(v___f_177_);
goto v___jp_178_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; lean_object* v_map_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_val_181_ = lean_ctor_get(v_old_x3f_175_, 0);
v___x_182_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_146_);
v_map_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_map_183_);
lean_dec_ref(v___x_182_);
v___x_184_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3));
v___x_185_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_183_, v___x_184_);
lean_dec(v_map_183_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_dec_ref(v___f_177_);
goto v___jp_178_;
}
else
{
lean_object* v_val_186_; 
v_val_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_val_186_);
lean_dec_ref_known(v___x_185_, 1);
if (lean_obj_tag(v_val_186_) == 1)
{
uint8_t v_v_187_; 
v_v_187_ = lean_ctor_get_uint8(v_val_186_, 0);
lean_dec_ref_known(v_val_186_, 0);
if (v_v_187_ == 0)
{
lean_dec_ref(v___f_177_);
goto v___jp_178_;
}
else
{
lean_object* v_stx_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_stx_188_ = lean_ctor_get(v_val_181_, 0);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_189_, 0, v___f_177_);
v___x_190_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4));
v___x_191_ = lean_box(0);
v___x_192_ = 0;
lean_inc(v_stx_188_);
v___x_193_ = l_Lean_Syntax_formatStx(v_stx_188_, v___x_191_, v___x_192_);
v___x_194_ = l_Std_Format_defWidth;
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = l_Std_Format_pretty(v___x_193_, v___x_194_, v___x_195_, v___x_195_);
v___x_197_ = lean_string_append(v___x_190_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_dbg_trace(v___x_197_, v___f_189_);
v___x_199_ = lean_unbox(v___x_198_);
lean_dec(v___x_198_);
v___y_172_ = v___x_199_;
goto v___jp_171_;
}
}
else
{
lean_dec(v_val_186_);
lean_dec_ref(v___f_177_);
goto v___jp_178_;
}
}
}
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
lean_dec_ref(v___f_177_);
v___x_200_ = lean_box(0);
v___x_201_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_200_);
v___y_172_ = v___x_201_;
goto v___jp_171_;
}
v___jp_178_:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_box(0);
v___x_180_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_179_);
v___y_172_ = v___x_180_;
goto v___jp_171_;
}
}
v___jp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_inc_ref(v_fixedTermElabs_166_);
lean_inc(v_sectionFVars_156_);
lean_inc(v_sectionVars_155_);
lean_inc_ref(v_autoBoundImplicitForbidden_154_);
lean_inc(v_autoBoundImplicitContext_153_);
lean_inc(v_macroStack_150_);
lean_inc(v_declName_x3f_149_);
v___x_169_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_169_, 0, v_declName_x3f_149_);
lean_ctor_set(v___x_169_, 1, v_macroStack_150_);
lean_ctor_set(v___x_169_, 2, v_autoBoundImplicitContext_153_);
lean_ctor_set(v___x_169_, 3, v_autoBoundImplicitForbidden_154_);
lean_ctor_set(v___x_169_, 4, v_sectionVars_155_);
lean_ctor_set(v___x_169_, 5, v_sectionFVars_156_);
lean_ctor_set(v___x_169_, 6, v___y_168_);
lean_ctor_set(v___x_169_, 7, v_fixedTermElabs_166_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8, v_mayPostpone_151_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 1, v_errToSorry_152_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 2, v_implicitLambda_157_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 3, v_heedElabAsElim_158_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 4, v_isNoncomputableSection_159_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 5, v_isMetaSection_160_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 6, v_ignoreTCFailures_161_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 7, v_inPattern_162_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_164_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_165_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc(v___y_141_);
lean_inc_ref(v___y_140_);
v___x_170_ = lean_apply_9(v_act_139_, v___y_140_, v___y_141_, v___x_169_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
return v___x_170_;
}
v___jp_171_:
{
if (v___y_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
v___y_168_ = v___x_173_;
goto v___jp_167_;
}
else
{
lean_inc(v_tacSnap_x3f_163_);
v___y_168_ = v_tacSnap_x3f_163_;
goto v___jp_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(lean_object* v_cond_202_, lean_object* v_act_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
uint8_t v_cond_boxed_213_; lean_object* v_res_214_; 
v_cond_boxed_213_ = lean_unbox(v_cond_202_);
v_res_214_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_boxed_213_, v_act_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(lean_object* v_00_u03b1_215_, uint8_t v_cond_216_, lean_object* v_act_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_216_, v_act_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(lean_object* v_00_u03b1_228_, lean_object* v_cond_229_, lean_object* v_act_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_cond_boxed_240_; lean_object* v_res_241_; 
v_cond_boxed_240_ = lean_unbox(v_cond_229_);
v_res_241_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(v_00_u03b1_228_, v_cond_boxed_240_, v_act_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object* v_k_242_, uint8_t v_mayPostpone_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_242_, v_mayPostpone_243_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object* v_k_254_, lean_object* v_mayPostpone_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v_mayPostpone_boxed_265_; lean_object* v_res_266_; 
v_mayPostpone_boxed_265_ = lean_unbox(v_mayPostpone_255_);
v_res_266_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(v_k_254_, v_mayPostpone_boxed_265_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object* v___f_267_, lean_object* v_k_268_, uint8_t v_mayPostpone_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v_recover_279_; 
v_recover_279_ = lean_ctor_get_uint8(v___y_270_, sizeof(void*)*1);
if (v_recover_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_k_268_);
v___x_280_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v___f_267_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; 
lean_dec_ref(v___f_267_);
v___x_281_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_268_, v_mayPostpone_269_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object* v___f_282_, lean_object* v_k_283_, lean_object* v_mayPostpone_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
uint8_t v_mayPostpone_boxed_294_; lean_object* v_res_295_; 
v_mayPostpone_boxed_294_ = lean_unbox(v_mayPostpone_284_);
v_res_295_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(v___f_282_, v_k_283_, v_mayPostpone_boxed_294_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object* v_k_296_, uint8_t v_mayPostpone_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___f_310_; uint8_t v___x_311_; lean_object* v___x_312_; 
v___x_307_ = lean_box(v_mayPostpone_297_);
lean_inc_ref(v_k_296_);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_308_, 0, v_k_296_);
lean_closure_set(v___f_308_, 1, v___x_307_);
v___x_309_ = lean_box(v_mayPostpone_297_);
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_310_, 0, v___f_308_);
lean_closure_set(v___f_310_, 1, v_k_296_);
lean_closure_set(v___f_310_, 2, v___x_309_);
v___x_311_ = 1;
v___x_312_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v___x_311_, v___f_310_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object* v_k_313_, lean_object* v_mayPostpone_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
uint8_t v_mayPostpone_boxed_324_; lean_object* v_res_325_; 
v_mayPostpone_boxed_324_ = lean_unbox(v_mayPostpone_314_);
v_res_325_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_313_, v_mayPostpone_boxed_324_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object* v_00_u03b1_326_, lean_object* v_k_327_, uint8_t v_mayPostpone_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_327_, v_mayPostpone_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object* v_00_u03b1_339_, lean_object* v_k_340_, lean_object* v_mayPostpone_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
uint8_t v_mayPostpone_boxed_351_; lean_object* v_res_352_; 
v_mayPostpone_boxed_351_ = lean_unbox(v_mayPostpone_341_);
v_res_352_ = l_Lean_Elab_Tactic_runTermElab(v_00_u03b1_339_, v_k_340_, v_mayPostpone_boxed_351_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(lean_object* v_e_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Lean_Expr_hasMVar(v_e_353_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_e_353_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v_mctx_359_; lean_object* v___x_360_; lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_363_; lean_object* v_cache_364_; lean_object* v_zetaDeltaFVarIds_365_; lean_object* v_postponed_366_; lean_object* v_diag_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_376_; 
v___x_358_ = lean_st_ref_get(v___y_354_);
v_mctx_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc_ref(v_mctx_359_);
lean_dec(v___x_358_);
v___x_360_ = l_Lean_instantiateMVarsCore(v_mctx_359_, v_e_353_);
v_fst_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_fst_361_);
v_snd_362_ = lean_ctor_get(v___x_360_, 1);
lean_inc(v_snd_362_);
lean_dec_ref(v___x_360_);
v___x_363_ = lean_st_ref_take(v___y_354_);
v_cache_364_ = lean_ctor_get(v___x_363_, 1);
v_zetaDeltaFVarIds_365_ = lean_ctor_get(v___x_363_, 2);
v_postponed_366_ = lean_ctor_get(v___x_363_, 3);
v_diag_367_ = lean_ctor_get(v___x_363_, 4);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_377_);
v___x_369_ = v___x_363_;
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_diag_367_);
lean_inc(v_postponed_366_);
lean_inc(v_zetaDeltaFVarIds_365_);
lean_inc(v_cache_364_);
lean_dec(v___x_363_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v_snd_362_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_snd_362_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_cache_364_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_zetaDeltaFVarIds_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_postponed_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_diag_367_);
v___x_372_ = v_reuseFailAlloc_375_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_st_ref_put(v___y_354_, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_fst_361_);
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(lean_object* v_e_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_378_, v___y_379_);
lean_dec(v___y_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(lean_object* v_e_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_382_, v___y_388_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(lean_object* v_e_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(v_e_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object* v_stx_404_, lean_object* v_expectedType_x3f_405_, uint8_t v_mayPostpone_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_toCold_420_; lean_object* v_currRecDepth_421_; lean_object* v_ref_422_; uint16_t v_optionFlags_423_; uint8_t v_suppressElabErrors_424_; uint8_t v_checkDeprecated_425_; uint8_t v_isRecordingDeps_426_; lean_object* v_ref_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_416_ = 1;
v___x_417_ = lean_box(v___x_416_);
v___x_418_ = lean_box(v___x_416_);
lean_inc(v_stx_404_);
v___x_419_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_419_, 0, v_stx_404_);
lean_closure_set(v___x_419_, 1, v_expectedType_x3f_405_);
lean_closure_set(v___x_419_, 2, v___x_417_);
lean_closure_set(v___x_419_, 3, v___x_418_);
v_toCold_420_ = lean_ctor_get(v_a_413_, 0);
v_currRecDepth_421_ = lean_ctor_get(v_a_413_, 1);
v_ref_422_ = lean_ctor_get(v_a_413_, 2);
v_optionFlags_423_ = lean_ctor_get_uint16(v_a_413_, sizeof(void*)*3);
v_suppressElabErrors_424_ = lean_ctor_get_uint8(v_a_413_, sizeof(void*)*3 + 2);
v_checkDeprecated_425_ = lean_ctor_get_uint8(v_a_413_, sizeof(void*)*3 + 3);
v_isRecordingDeps_426_ = lean_ctor_get_uint8(v_a_413_, sizeof(void*)*3 + 4);
v_ref_427_ = l_Lean_replaceRef(v_stx_404_, v_ref_422_);
lean_dec(v_stx_404_);
lean_inc(v_currRecDepth_421_);
lean_inc_ref(v_toCold_420_);
v___x_428_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_428_, 0, v_toCold_420_);
lean_ctor_set(v___x_428_, 1, v_currRecDepth_421_);
lean_ctor_set(v___x_428_, 2, v_ref_427_);
lean_ctor_set_uint16(v___x_428_, sizeof(void*)*3, v_optionFlags_423_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 2, v_suppressElabErrors_424_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 3, v_checkDeprecated_425_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 4, v_isRecordingDeps_426_);
v___x_429_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___x_419_, v_mayPostpone_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v___x_428_, v_a_414_);
lean_dec_ref_known(v___x_428_, 3);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_430_, v_a_412_);
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
lean_object* v_a_462_; lean_object* v___x_463_; uint8_t v_foApprox_464_; uint8_t v_ctxApprox_465_; uint8_t v_quasiPatternApprox_466_; uint8_t v_constApprox_467_; uint8_t v_isDefEqStuckEx_468_; uint8_t v_unificationHints_469_; uint8_t v_proofIrrelevance_470_; uint8_t v_offsetCnstrs_471_; uint8_t v_transparency_472_; uint8_t v_etaStruct_473_; uint8_t v_univApprox_474_; uint8_t v_iota_475_; uint8_t v_beta_476_; uint8_t v_proj_477_; uint8_t v_zeta_478_; uint8_t v_zetaDelta_479_; uint8_t v_zetaUnused_480_; uint8_t v_zetaHave_481_; uint8_t v_canUnfoldPredicateConfig_482_; uint8_t v_stringLitToCtor_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_540_; 
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
v_stringLitToCtor_483_ = lean_ctor_get_uint8(v___x_463_, 20);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_540_ == 0)
{
v___x_485_ = v___x_463_;
v_isShared_486_ = v_isSharedCheck_540_;
goto v_resetjp_484_;
}
else
{
lean_dec(v___x_463_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_540_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v_trackZetaDelta_487_; lean_object* v_zetaDeltaSet_488_; lean_object* v_lctx_489_; lean_object* v_localInstances_490_; lean_object* v_defEqCtx_x3f_491_; lean_object* v_synthPendingDepth_492_; lean_object* v_customCanUnfoldPredicate_x3f_493_; uint8_t v_univApprox_494_; uint8_t v_inTypeClassResolution_495_; uint8_t v_cacheInferType_496_; uint8_t v___x_497_; lean_object* v___x_499_; 
v_trackZetaDelta_487_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7);
v_zetaDeltaSet_488_ = lean_ctor_get(v_a_453_, 1);
v_lctx_489_ = lean_ctor_get(v_a_453_, 2);
v_localInstances_490_ = lean_ctor_get(v_a_453_, 3);
v_defEqCtx_x3f_491_ = lean_ctor_get(v_a_453_, 4);
v_synthPendingDepth_492_ = lean_ctor_get(v_a_453_, 5);
v_customCanUnfoldPredicate_x3f_493_ = lean_ctor_get(v_a_453_, 6);
v_univApprox_494_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_495_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7 + 2);
v_cacheInferType_496_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*7 + 3);
v___x_497_ = 1;
if (v_isShared_486_ == 0)
{
v___x_499_ = v___x_485_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 0, v_foApprox_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 1, v_ctxApprox_465_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 2, v_quasiPatternApprox_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 3, v_constApprox_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 4, v_isDefEqStuckEx_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 5, v_unificationHints_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 6, v_proofIrrelevance_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 8, v_offsetCnstrs_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 9, v_transparency_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 10, v_etaStruct_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 11, v_univApprox_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 12, v_iota_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 13, v_beta_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 14, v_proj_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 15, v_zeta_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 16, v_zetaDelta_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 17, v_zetaUnused_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 18, v_zetaHave_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 19, v_canUnfoldPredicateConfig_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, 20, v_stringLitToCtor_483_);
v___x_499_ = v_reuseFailAlloc_539_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
uint64_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_ctor_set_uint8(v___x_499_, 7, v___x_497_);
v___x_500_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set_uint64(v___x_501_, sizeof(void*)*1, v___x_500_);
lean_inc(v_customCanUnfoldPredicate_x3f_493_);
lean_inc(v_synthPendingDepth_492_);
lean_inc(v_defEqCtx_x3f_491_);
lean_inc_ref(v_localInstances_490_);
lean_inc_ref(v_lctx_489_);
lean_inc(v_zetaDeltaSet_488_);
v___x_502_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_zetaDeltaSet_488_);
lean_ctor_set(v___x_502_, 2, v_lctx_489_);
lean_ctor_set(v___x_502_, 3, v_localInstances_490_);
lean_ctor_set(v___x_502_, 4, v_defEqCtx_x3f_491_);
lean_ctor_set(v___x_502_, 5, v_synthPendingDepth_492_);
lean_ctor_set(v___x_502_, 6, v_customCanUnfoldPredicate_x3f_493_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7, v_trackZetaDelta_487_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 1, v_univApprox_494_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 2, v_inTypeClassResolution_495_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 3, v_cacheInferType_496_);
lean_inc(v_val_460_);
lean_inc(v_a_462_);
v___x_503_ = l_Lean_Meta_isExprDefEq(v_a_462_, v_val_460_, v___x_502_, v_a_454_, v_a_455_, v_a_456_);
lean_dec_ref_known(v___x_502_, 7);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_530_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_530_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_530_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_530_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_del_object(v___x_506_);
v___x_509_ = lean_box(0);
lean_inc(v_a_459_);
v___x_510_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_509_, v_val_460_, v_a_462_, v_a_459_, v___x_509_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_510_, 0);
lean_dec(v_unused_518_);
v___x_512_ = v___x_510_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_dec(v___x_510_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_a_459_);
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_459_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_459_);
v_a_519_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v_a_462_);
lean_dec(v_val_460_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v_a_459_);
v___x_528_ = v___x_506_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_459_);
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
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_462_);
lean_dec(v_val_460_);
lean_dec(v_a_459_);
v_a_531_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_503_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_503_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* v_stx_541_, lean_object* v_expectedType_x3f_542_, lean_object* v_mayPostpone_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
uint8_t v_mayPostpone_boxed_553_; lean_object* v_res_554_; 
v_mayPostpone_boxed_553_ = lean_unbox(v_mayPostpone_543_);
v_res_554_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_stx_541_, v_expectedType_x3f_542_, v_mayPostpone_boxed_553_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_Elab_abortTacticExceptionId;
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object* v_00_u03b1_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object* v_00_u03b1_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(v_00_u03b1_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object* v_mvarIds_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_mvarIds_585_, v___x_595_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_607_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___x_601_; 
v___x_601_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
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
lean_object* v___x_606_; 
lean_del_object(v___x_599_);
v___x_606_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_606_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_596_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_596_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* v_mvarIds_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_mvarIds_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec_ref(v_mvarIds_616_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object* v___x_627_, lean_object* v_mvarCounterSaved_628_, lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_, lean_object* v_b_632_){
_start:
{
lean_object* v___y_634_; uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_eq(v_i_630_, v_stop_631_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_index_641_; uint8_t v___x_642_; 
v___x_639_ = lean_array_uget_borrowed(v_as_629_, v_i_630_);
lean_inc(v___x_639_);
v___x_640_ = l_Lean_MetavarContext_getDecl(v___x_627_, v___x_639_);
v_index_641_ = lean_ctor_get(v___x_640_, 6);
lean_inc(v_index_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_nat_dec_le(v_mvarCounterSaved_628_, v_index_641_);
lean_dec(v_index_641_);
if (v___x_642_ == 0)
{
v___y_634_ = v_b_632_;
goto v___jp_633_;
}
else
{
lean_object* v___x_643_; 
lean_inc(v___x_639_);
v___x_643_ = lean_array_push(v_b_632_, v___x_639_);
v___y_634_ = v___x_643_;
goto v___jp_633_;
}
}
else
{
return v_b_632_;
}
v___jp_633_:
{
size_t v___x_635_; size_t v___x_636_; 
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_630_, v___x_635_);
v_i_630_ = v___x_636_;
v_b_632_ = v___y_634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object* v___x_644_, lean_object* v_mvarCounterSaved_645_, lean_object* v_as_646_, lean_object* v_i_647_, lean_object* v_stop_648_, lean_object* v_b_649_){
_start:
{
size_t v_i_boxed_650_; size_t v_stop_boxed_651_; lean_object* v_res_652_; 
v_i_boxed_650_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_stop_boxed_651_ = lean_unbox_usize(v_stop_648_);
lean_dec(v_stop_648_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v___x_644_, v_mvarCounterSaved_645_, v_as_646_, v_i_boxed_650_, v_stop_boxed_651_, v_b_649_);
lean_dec_ref(v_as_646_);
lean_dec(v_mvarCounterSaved_645_);
lean_dec_ref(v___x_644_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object* v_mvarIds_655_, lean_object* v_mvarCounterSaved_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_659_ = lean_st_ref_get(v_a_657_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_mvarIds_655_);
v___x_662_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_663_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v___x_659_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
return v___x_664_;
}
else
{
lean_object* v_mctx_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_mctx_665_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_mctx_665_);
lean_dec(v___x_659_);
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_661_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_665_, v_mvarCounterSaved_656_, v_mvarIds_655_, v___x_666_, v___x_667_, v___x_662_);
lean_dec_ref(v_mctx_665_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object* v_mvarIds_670_, lean_object* v_mvarCounterSaved_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_670_, v_mvarCounterSaved_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec(v_mvarCounterSaved_671_);
lean_dec_ref(v_mvarIds_670_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* v_mvarIds_675_, lean_object* v_mvarCounterSaved_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_675_, v_mvarCounterSaved_676_, v_a_678_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* v_mvarIds_683_, lean_object* v_mvarCounterSaved_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Elab_Tactic_filterOldMVars(v_mvarIds_683_, v_mvarCounterSaved_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_mvarCounterSaved_684_);
lean_dec_ref(v_mvarIds_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
v___x_701_ = lean_apply_9(v_x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object* v_mvarId_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___f_724_; lean_object* v___x_725_; 
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_724_, 0, v_x_714_);
lean_closure_set(v___f_724_, 1, v___y_715_);
lean_closure_set(v___f_724_, 2, v___y_716_);
lean_closure_set(v___f_724_, 3, v___y_717_);
lean_closure_set(v___f_724_, 4, v___y_718_);
v___x_725_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_713_, v___f_724_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_725_) == 0)
{
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object* v_mvarId_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_734_, v_x_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object* v_00_u03b1_746_, lean_object* v_mvarId_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_747_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object* v_00_u03b1_759_, lean_object* v_mvarId_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(v_00_u03b1_759_, v_mvarId_760_, v_x_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_771_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object* v_a_778_, lean_object* v_x_779_, lean_object* v_tacName_780_, uint8_t v_checkNewUnassigned_781_, lean_object* v_mvarCounter_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
lean_inc(v_a_778_);
v___x_792_ = l_Lean_MVarId_getType(v_a_778_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
lean_inc(v_a_778_);
v___x_794_ = l_Lean_MVarId_getTag(v_a_778_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
v___x_796_ = lean_apply_11(v_x_779_, v_a_793_, v_a_795_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, lean_box(0));
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
if (v_checkNewUnassigned_781_ == 0)
{
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
v___y_799_ = v___y_787_;
v___y_800_ = v___y_788_;
v___y_801_ = v___y_789_;
v___y_802_ = v___y_790_;
goto v___jp_798_;
}
else
{
lean_object* v___x_829_; 
lean_inc(v_a_797_);
v___x_829_ = l_Lean_Meta_getMVars(v_a_797_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_830_, v_mvarCounter_782_, v___y_788_);
lean_dec(v_a_830_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
v___x_833_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_832_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_a_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_dec_ref_known(v___x_833_, 1);
v___y_799_ = v___y_787_;
v___y_800_ = v___y_788_;
v___y_801_ = v___y_789_;
v___y_802_ = v___y_790_;
goto v___jp_798_;
}
else
{
lean_dec(v_a_797_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v_tacName_780_);
lean_dec(v_a_778_);
return v___x_833_;
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_797_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_tacName_780_);
lean_dec(v_a_778_);
v_a_834_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_829_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_829_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
v___jp_798_:
{
lean_object* v___x_803_; 
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
lean_inc(v_a_797_);
lean_inc(v_a_778_);
v___x_803_ = lean_checked_assign(v_a_778_, v_a_797_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_820_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_820_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_820_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_820_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; 
v___x_808_ = lean_unbox(v_a_804_);
lean_dec(v_a_804_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_del_object(v___x_806_);
v___x_809_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1);
v___x_810_ = l_Lean_indentExpr(v_a_797_);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_Meta_throwTacticEx___redArg(v_tacName_780_, v_a_778_, v___x_814_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v_a_797_);
lean_dec(v_tacName_780_);
lean_dec(v_a_778_);
v___x_816_ = lean_box(0);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_816_);
v___x_818_ = v___x_806_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v_a_797_);
lean_dec(v_tacName_780_);
lean_dec(v_a_778_);
v_a_821_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_803_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_803_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_tacName_780_);
lean_dec(v_a_778_);
v_a_842_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_796_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_796_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_793_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_tacName_780_);
lean_dec_ref(v_x_779_);
lean_dec(v_a_778_);
v_a_850_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_794_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_794_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_tacName_780_);
lean_dec_ref(v_x_779_);
lean_dec(v_a_778_);
v_a_858_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_792_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_792_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object* v_a_866_, lean_object* v_x_867_, lean_object* v_tacName_868_, lean_object* v_checkNewUnassigned_869_, lean_object* v_mvarCounter_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_880_; lean_object* v_res_881_; 
v_checkNewUnassigned_boxed_880_ = lean_unbox(v_checkNewUnassigned_869_);
v_res_881_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(v_a_866_, v_x_867_, v_tacName_868_, v_checkNewUnassigned_boxed_880_, v_mvarCounter_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v_mvarCounter_870_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* v_tacName_882_, lean_object* v_x_883_, uint8_t v_checkNewUnassigned_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_mctx_895_; lean_object* v_mvarCounter_896_; lean_object* v___x_897_; 
v___x_894_ = lean_st_ref_get(v_a_890_);
v_mctx_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_mctx_895_);
lean_dec(v___x_894_);
v_mvarCounter_896_ = lean_ctor_get(v_mctx_895_, 3);
lean_inc(v_mvarCounter_896_);
lean_dec_ref(v_mctx_895_);
v___x_897_ = l_Lean_Elab_Tactic_popMainGoal___redArg(v_a_886_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___f_900_; lean_object* v___x_901_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_n(v_a_898_, 3);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_box(v_checkNewUnassigned_884_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed), 14, 5);
lean_closure_set(v___f_900_, 0, v_a_898_);
lean_closure_set(v___f_900_, 1, v_x_883_);
lean_closure_set(v___f_900_, 2, v_tacName_882_);
lean_closure_set(v___f_900_, 3, v___x_899_);
lean_closure_set(v___f_900_, 4, v_mvarCounter_896_);
v___x_901_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_a_898_, v___f_900_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_dec(v_a_898_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; uint8_t v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v___x_903_ = l_Lean_Exception_isInterrupt(v_a_902_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
lean_inc(v_a_902_);
v___x_904_ = l_Lean_Exception_isRuntime(v_a_902_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_905_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_898_, v_a_886_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_905_, 0);
lean_dec(v_unused_913_);
v___x_907_ = v___x_905_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_dec(v___x_905_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
lean_ctor_set(v___x_907_, 0, v_a_902_);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_902_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
else
{
lean_dec(v_a_902_);
return v___x_905_;
}
}
else
{
lean_dec(v_a_898_);
return v___x_901_;
}
}
else
{
lean_dec(v_a_898_);
return v___x_901_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_mvarCounter_896_);
lean_dec_ref(v_x_883_);
lean_dec(v_tacName_882_);
v_a_914_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_897_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_897_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* v_tacName_922_, lean_object* v_x_923_, lean_object* v_checkNewUnassigned_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_934_; lean_object* v_res_935_; 
v_checkNewUnassigned_boxed_934_ = lean_unbox(v_checkNewUnassigned_924_);
v_res_935_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacName_922_, v_x_923_, v_checkNewUnassigned_boxed_934_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_box(0);
v___x_937_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object* v_00_u03b1_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object* v_00_u03b1_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(v_00_u03b1_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object* v___x_966_, lean_object* v_type_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_type_967_);
v___x_979_ = 0;
v___x_980_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_966_, v___x_978_, v___x_979_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object* v___x_981_, lean_object* v_type_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Elab_Tactic_evalExact___lam__0(v___x_981_, v_type_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v_x_983_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* v_stx_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
lean_inc(v_stx_1005_);
v___x_1016_ = l_Lean_Syntax_isOfKind(v_stx_1005_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_dec(v_stx_1005_);
v___x_1017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = l_Lean_Syntax_getArg(v_stx_1005_, v___x_1018_);
lean_dec(v_stx_1005_);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1020_, 0, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__5));
v___x_1022_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_1021_, v___f_1020_, v___x_1016_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object* v_stx_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Elab_Tactic_evalExact(v_stx_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1041_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1042_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
v___x_1043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1044_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___boxed), 10, 0);
v___x_1045_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1041_, v___x_1042_, v___x_1043_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1075_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6));
v___x_1076_ = l_Lean_addBuiltinDeclarationRanges(v___x_1074_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
return v_res_1078_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object* v_mctx_1079_, lean_object* v_mvarId_u2081_1080_, lean_object* v_mvarId_u2082_1081_){
_start:
{
lean_object* v_decl_u2081_1082_; lean_object* v_index_1083_; lean_object* v_decl_u2082_1084_; lean_object* v_index_1085_; uint8_t v___x_1086_; 
lean_inc(v_mvarId_u2081_1080_);
v_decl_u2081_1082_ = l_Lean_MetavarContext_getDecl(v_mctx_1079_, v_mvarId_u2081_1080_);
v_index_1083_ = lean_ctor_get(v_decl_u2081_1082_, 6);
lean_inc(v_index_1083_);
lean_dec_ref(v_decl_u2081_1082_);
lean_inc(v_mvarId_u2082_1081_);
v_decl_u2082_1084_ = l_Lean_MetavarContext_getDecl(v_mctx_1079_, v_mvarId_u2082_1081_);
v_index_1085_ = lean_ctor_get(v_decl_u2082_1084_, 6);
lean_inc(v_index_1085_);
lean_dec_ref(v_decl_u2082_1084_);
v___x_1086_ = lean_nat_dec_eq(v_index_1083_, v_index_1085_);
if (v___x_1086_ == 0)
{
uint8_t v___x_1087_; 
lean_dec(v_mvarId_u2082_1081_);
lean_dec(v_mvarId_u2081_1080_);
v___x_1087_ = lean_nat_dec_lt(v_index_1083_, v_index_1085_);
lean_dec(v_index_1085_);
lean_dec(v_index_1083_);
return v___x_1087_;
}
else
{
uint8_t v___x_1088_; 
lean_dec(v_index_1085_);
lean_dec(v_index_1083_);
v___x_1088_ = l_Lean_Name_quickLt(v_mvarId_u2081_1080_, v_mvarId_u2082_1081_);
lean_dec(v_mvarId_u2082_1081_);
lean_dec(v_mvarId_u2081_1080_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object* v_mctx_1089_, lean_object* v_mvarId_u2081_1090_, lean_object* v_mvarId_u2082_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(v_mctx_1089_, v_mvarId_u2081_1090_, v_mvarId_u2082_1091_);
lean_dec_ref(v_mctx_1089_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object* v_mvarIds_1094_, lean_object* v_toPure_1095_, lean_object* v_mctx_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = lean_array_get_size(v_mvarIds_1094_);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_nat_dec_eq(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___f_1100_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___y_1109_; uint8_t v___x_1111_; 
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1100_, 0, v_mctx_1096_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_sub(v___x_1097_, v___x_1106_);
v___x_1111_ = lean_nat_dec_le(v___x_1098_, v___x_1107_);
if (v___x_1111_ == 0)
{
lean_inc(v___x_1107_);
v___y_1109_ = v___x_1107_;
goto v___jp_1108_;
}
else
{
v___y_1109_ = v___x_1098_;
goto v___jp_1108_;
}
v___jp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1100_, v___x_1097_, v_mvarIds_1094_, v___y_1102_, v___y_1103_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1103_);
v___x_1105_ = lean_apply_2(v_toPure_1095_, lean_box(0), v___x_1104_);
return v___x_1105_;
}
v___jp_1108_:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_nat_dec_le(v___y_1109_, v___x_1107_);
if (v___x_1110_ == 0)
{
lean_dec(v___x_1107_);
lean_inc(v___y_1109_);
v___y_1102_ = v___y_1109_;
v___y_1103_ = v___y_1109_;
goto v___jp_1101_;
}
else
{
v___y_1102_ = v___y_1109_;
v___y_1103_ = v___x_1107_;
goto v___jp_1101_;
}
}
}
else
{
lean_object* v___x_1112_; 
lean_dec_ref(v_mctx_1096_);
v___x_1112_ = lean_apply_2(v_toPure_1095_, lean_box(0), v_mvarIds_1094_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_mvarIds_1115_){
_start:
{
lean_object* v_toApplicative_1116_; lean_object* v_toBind_1117_; lean_object* v_getMCtx_1118_; lean_object* v_toPure_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; 
v_toApplicative_1116_ = lean_ctor_get(v_inst_1114_, 0);
lean_inc_ref(v_toApplicative_1116_);
v_toBind_1117_ = lean_ctor_get(v_inst_1114_, 1);
lean_inc(v_toBind_1117_);
lean_dec_ref(v_inst_1114_);
v_getMCtx_1118_ = lean_ctor_get(v_inst_1113_, 0);
lean_inc(v_getMCtx_1118_);
lean_dec_ref(v_inst_1113_);
v_toPure_1119_ = lean_ctor_get(v_toApplicative_1116_, 1);
lean_inc(v_toPure_1119_);
lean_dec_ref(v_toApplicative_1116_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1120_, 0, v_mvarIds_1115_);
lean_closure_set(v___f_1120_, 1, v_toPure_1119_);
v___x_1121_ = lean_apply_4(v_toBind_1117_, lean_box(0), lean_box(0), v_getMCtx_1118_, v___f_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* v_m_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_mvarIds_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1123_, v_inst_1124_, v_mvarIds_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_mvarIds_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1127_, v_inst_1128_, v_mvarIds_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* v_m_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_mvarIds_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1132_, v_inst_1133_, v_mvarIds_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v_mctx_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_st_ref_get(v___y_1137_);
v_mctx_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_mctx_1142_);
lean_dec(v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_mctx_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object* v_val_1150_, lean_object* v_toPure_1151_, lean_object* v_newMVarIds_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_val_1150_);
lean_ctor_set(v___x_1153_, 1, v_newMVarIds_1152_);
v___x_1154_ = lean_apply_2(v_toPure_1151_, lean_box(0), v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v_inst_1157_, lean_object* v_toBind_1158_, lean_object* v___f_1159_, lean_object* v_newMVarIds_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v___x_1155_, v___x_1156_, v_newMVarIds_1160_);
v___x_1162_ = lean_apply_2(v_inst_1157_, lean_box(0), v___x_1161_);
v___x_1163_ = lean_apply_4(v_toBind_1158_, lean_box(0), lean_box(0), v___x_1162_, v___f_1159_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object* v_mvarCounter_1164_, lean_object* v_inst_1165_, lean_object* v_toBind_1166_, lean_object* v___f_1167_, lean_object* v_newMVarIds_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_filterOldMVars___boxed), 7, 2);
lean_closure_set(v___x_1169_, 0, v_newMVarIds_1168_);
lean_closure_set(v___x_1169_, 1, v_mvarCounter_1164_);
v___x_1170_ = lean_apply_2(v_inst_1165_, lean_box(0), v___x_1169_);
v___x_1171_ = lean_apply_4(v_toBind_1166_, lean_box(0), lean_box(0), v___x_1170_, v___f_1167_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object* v_toPure_1172_, lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v_inst_1175_, lean_object* v_toBind_1176_, lean_object* v_mvarCounter_1177_, lean_object* v_val_1178_){
_start:
{
lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_inc_ref(v_val_1178_);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1179_, 0, v_val_1178_);
lean_closure_set(v___f_1179_, 1, v_toPure_1172_);
lean_inc_n(v_toBind_1176_, 2);
lean_inc_n(v_inst_1175_, 2);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1180_, 0, v___x_1173_);
lean_closure_set(v___f_1180_, 1, v___x_1174_);
lean_closure_set(v___f_1180_, 2, v_inst_1175_);
lean_closure_set(v___f_1180_, 3, v_toBind_1176_);
lean_closure_set(v___f_1180_, 4, v___f_1179_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1181_, 0, v_mvarCounter_1177_);
lean_closure_set(v___f_1181_, 1, v_inst_1175_);
lean_closure_set(v___f_1181_, 2, v_toBind_1176_);
lean_closure_set(v___f_1181_, 3, v___f_1180_);
v___x_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_getMVarsNoDelayed___boxed), 6, 1);
lean_closure_set(v___x_1182_, 0, v_val_1178_);
v___x_1183_ = lean_apply_2(v_inst_1175_, lean_box(0), v___x_1182_);
v___x_1184_ = lean_apply_4(v_toBind_1176_, lean_box(0), lean_box(0), v___x_1183_, v___f_1181_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object* v_toPure_1185_, lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v_inst_1188_, lean_object* v_toBind_1189_, lean_object* v_k_1190_, lean_object* v_____do__lift_1191_){
_start:
{
lean_object* v_mvarCounter_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; 
v_mvarCounter_1192_ = lean_ctor_get(v_____do__lift_1191_, 3);
lean_inc(v_mvarCounter_1192_);
lean_dec_ref(v_____do__lift_1191_);
lean_inc(v_toBind_1189_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1193_, 0, v_toPure_1185_);
lean_closure_set(v___f_1193_, 1, v___x_1186_);
lean_closure_set(v___f_1193_, 2, v___x_1187_);
lean_closure_set(v___f_1193_, 3, v_inst_1188_);
lean_closure_set(v___f_1193_, 4, v_toBind_1189_);
lean_closure_set(v___f_1193_, 5, v_mvarCounter_1192_);
v___x_1194_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v_k_1190_, v___f_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_instMonadEIO___redArg();
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0);
v___x_1197_ = l_StateRefT_x27_instMonad___redArg(v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_toApplicative_1208_; lean_object* v_toFunctor_1209_; lean_object* v_toSeq_1210_; lean_object* v_toSeqLeft_1211_; lean_object* v_toSeqRight_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_toApplicative_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1258_; 
v___x_1206_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_1207_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1);
v_toApplicative_1208_ = lean_ctor_get(v___x_1207_, 0);
v_toFunctor_1209_ = lean_ctor_get(v_toApplicative_1208_, 0);
v_toSeq_1210_ = lean_ctor_get(v_toApplicative_1208_, 2);
v_toSeqLeft_1211_ = lean_ctor_get(v_toApplicative_1208_, 3);
v_toSeqRight_1212_ = lean_ctor_get(v_toApplicative_1208_, 4);
v___f_1213_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2));
v___f_1214_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1209_, 2);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toFunctor_1209_);
v___f_1216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1216_, 0, v_toFunctor_1209_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___f_1215_);
lean_ctor_set(v___x_1217_, 1, v___f_1216_);
lean_inc(v_toSeqRight_1212_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toSeqRight_1212_);
lean_inc(v_toSeqLeft_1211_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeqLeft_1211_);
lean_inc(v_toSeq_1210_);
v___f_1220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1220_, 0, v_toSeq_1210_);
v___x_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1217_);
lean_ctor_set(v___x_1221_, 1, v___f_1213_);
lean_ctor_set(v___x_1221_, 2, v___f_1220_);
lean_ctor_set(v___x_1221_, 3, v___f_1219_);
lean_ctor_set(v___x_1221_, 4, v___f_1218_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___f_1214_);
v___x_1223_ = l_StateRefT_x27_instMonad___redArg(v___x_1222_);
v_toApplicative_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1223_, 1);
lean_dec(v_unused_1259_);
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1258_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_toApplicative_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1258_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_toFunctor_1228_; lean_object* v_toSeq_1229_; lean_object* v_toSeqLeft_1230_; lean_object* v_toSeqRight_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1256_; 
v_toFunctor_1228_ = lean_ctor_get(v_toApplicative_1224_, 0);
v_toSeq_1229_ = lean_ctor_get(v_toApplicative_1224_, 2);
v_toSeqLeft_1230_ = lean_ctor_get(v_toApplicative_1224_, 3);
v_toSeqRight_1231_ = lean_ctor_get(v_toApplicative_1224_, 4);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_toApplicative_1224_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_toApplicative_1224_, 1);
lean_dec(v_unused_1257_);
v___x_1233_ = v_toApplicative_1224_;
v_isShared_1234_ = v_isSharedCheck_1256_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_toSeqRight_1231_);
lean_inc(v_toSeqLeft_1230_);
lean_inc(v_toSeq_1229_);
lean_inc(v_toFunctor_1228_);
lean_dec(v_toApplicative_1224_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1256_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1244_; 
v___f_1235_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4));
v___f_1236_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_1228_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toFunctor_1228_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toFunctor_1228_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___f_1237_);
lean_ctor_set(v___x_1239_, 1, v___f_1238_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeqRight_1231_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toSeqLeft_1230_);
v___f_1242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1242_, 0, v_toSeq_1229_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v___f_1240_);
lean_ctor_set(v___x_1233_, 3, v___f_1241_);
lean_ctor_set(v___x_1233_, 2, v___f_1242_);
lean_ctor_set(v___x_1233_, 1, v___f_1235_);
lean_ctor_set(v___x_1233_, 0, v___x_1239_);
v___x_1244_ = v___x_1233_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v___f_1241_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v___f_1240_);
v___x_1244_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___f_1236_);
lean_ctor_set(v___x_1226_, 0, v___x_1244_);
v___x_1246_ = v___x_1226_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___f_1236_);
v___x_1246_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v_toApplicative_1247_; lean_object* v_toBind_1248_; lean_object* v_toPure_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; 
v_toApplicative_1247_ = lean_ctor_get(v_inst_1203_, 0);
lean_inc_ref(v_toApplicative_1247_);
v_toBind_1248_ = lean_ctor_get(v_inst_1203_, 1);
lean_inc_n(v_toBind_1248_, 2);
lean_dec_ref(v_inst_1203_);
v_toPure_1249_ = lean_ctor_get(v_toApplicative_1247_, 1);
lean_inc(v_toPure_1249_);
lean_dec_ref(v_toApplicative_1247_);
v___f_1250_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6));
lean_inc(v_inst_1204_);
v___x_1251_ = lean_apply_2(v_inst_1204_, lean_box(0), v___f_1250_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5), 7, 6);
lean_closure_set(v___f_1252_, 0, v_toPure_1249_);
lean_closure_set(v___f_1252_, 1, v___x_1206_);
lean_closure_set(v___f_1252_, 2, v___x_1246_);
lean_closure_set(v___f_1252_, 3, v_inst_1204_);
lean_closure_set(v___f_1252_, 4, v_toBind_1248_);
lean_closure_set(v___f_1252_, 5, v_k_1205_);
v___x_1253_ = lean_apply_4(v_toBind_1248_, lean_box(0), lean_box(0), v___x_1251_, v___f_1252_);
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object* v_m_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_k_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg(v_inst_1261_, v_inst_1262_, v_k_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object* v_as_1265_, size_t v_i_1266_, size_t v_stop_1267_, lean_object* v_b_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_a_1277_; uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_eq(v_i_1266_, v_stop_1267_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_array_uget_borrowed(v_as_1265_, v_i_1266_);
lean_inc(v___x_1282_);
v___x_1283_ = l_Lean_Elab_Term_isLetRecAuxMVar(v___x_1282_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; uint8_t v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = lean_unbox(v_a_1284_);
lean_dec(v_a_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_inc(v___x_1282_);
v___x_1286_ = lean_array_push(v_b_1268_, v___x_1282_);
v_a_1277_ = v___x_1286_;
goto v___jp_1276_;
}
else
{
v_a_1277_ = v_b_1268_;
goto v___jp_1276_;
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_b_1268_);
v_a_1287_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1283_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1283_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_b_1268_);
return v___x_1295_;
}
v___jp_1276_:
{
size_t v___x_1278_; size_t v___x_1279_; 
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_add(v_i_1266_, v___x_1278_);
v_i_1266_ = v___x_1279_;
v_b_1268_ = v_a_1277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object* v_as_1296_, lean_object* v_i_1297_, lean_object* v_stop_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_i_boxed_1307_; size_t v_stop_boxed_1308_; lean_object* v_res_1309_; 
v_i_boxed_1307_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_stop_boxed_1308_ = lean_unbox_usize(v_stop_1298_);
lean_dec(v_stop_1298_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1296_, v_i_boxed_1307_, v_stop_boxed_1308_, v_b_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_as_1296_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object* v_as_1310_, size_t v_i_1311_, size_t v_stop_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_a_1320_; uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_eq(v_i_1311_, v_stop_1312_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_array_uget_borrowed(v_as_1310_, v_i_1311_);
lean_inc(v___x_1325_);
v___x_1326_ = l_Lean_MVarId_getKind(v___x_1325_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; uint8_t v___x_1328_; uint8_t v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = lean_unbox(v_a_1327_);
lean_dec(v_a_1327_);
v___x_1329_ = l_Lean_MetavarKind_isNatural(v___x_1328_);
if (v___x_1329_ == 0)
{
v_a_1320_ = v_b_1313_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1330_; 
lean_inc(v___x_1325_);
v___x_1330_ = lean_array_push(v_b_1313_, v___x_1325_);
v_a_1320_ = v___x_1330_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_b_1313_);
v_a_1331_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1326_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1326_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1313_);
return v___x_1339_;
}
v___jp_1319_:
{
size_t v___x_1321_; size_t v___x_1322_; 
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_add(v_i_1311_, v___x_1321_);
v_i_1311_ = v___x_1322_;
v_b_1313_ = v_a_1320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object* v_as_1340_, lean_object* v_i_1341_, lean_object* v_stop_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
size_t v_i_boxed_1349_; size_t v_stop_boxed_1350_; lean_object* v_res_1351_; 
v_i_boxed_1349_ = lean_unbox_usize(v_i_1341_);
lean_dec(v_i_1341_);
v_stop_boxed_1350_ = lean_unbox_usize(v_stop_1342_);
lean_dec(v_stop_1342_);
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1340_, v_i_boxed_1349_, v_stop_boxed_1350_, v_b_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_as_1340_);
return v_res_1351_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___x_1352_, lean_object* v_mvarId_u2081_1353_, lean_object* v_mvarId_u2082_1354_){
_start:
{
lean_object* v_decl_u2081_1355_; lean_object* v_index_1356_; lean_object* v_decl_u2082_1357_; lean_object* v_index_1358_; uint8_t v___x_1359_; 
lean_inc(v_mvarId_u2081_1353_);
v_decl_u2081_1355_ = l_Lean_MetavarContext_getDecl(v___x_1352_, v_mvarId_u2081_1353_);
v_index_1356_ = lean_ctor_get(v_decl_u2081_1355_, 6);
lean_inc(v_index_1356_);
lean_dec_ref(v_decl_u2081_1355_);
lean_inc(v_mvarId_u2082_1354_);
v_decl_u2082_1357_ = l_Lean_MetavarContext_getDecl(v___x_1352_, v_mvarId_u2082_1354_);
v_index_1358_ = lean_ctor_get(v_decl_u2082_1357_, 6);
lean_inc(v_index_1358_);
lean_dec_ref(v_decl_u2082_1357_);
v___x_1359_ = lean_nat_dec_eq(v_index_1356_, v_index_1358_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
lean_dec(v_mvarId_u2082_1354_);
lean_dec(v_mvarId_u2081_1353_);
v___x_1360_ = lean_nat_dec_lt(v_index_1356_, v_index_1358_);
lean_dec(v_index_1358_);
lean_dec(v_index_1356_);
return v___x_1360_;
}
else
{
uint8_t v___x_1361_; 
lean_dec(v_index_1358_);
lean_dec(v_index_1356_);
v___x_1361_ = l_Lean_Name_quickLt(v_mvarId_u2081_1353_, v_mvarId_u2082_1354_);
lean_dec(v_mvarId_u2082_1354_);
lean_dec(v_mvarId_u2081_1353_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_1362_, lean_object* v_mvarId_u2081_1363_, lean_object* v_mvarId_u2082_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1362_, v_mvarId_u2081_1363_, v_mvarId_u2082_1364_);
lean_dec_ref(v___x_1362_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_1367_, lean_object* v_hi_1368_, lean_object* v_pivot_1369_, lean_object* v_as_1370_, lean_object* v_i_1371_, lean_object* v_k_1372_){
_start:
{
uint8_t v___y_1374_; uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_lt(v_k_1372_, v_hi_1368_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v_k_1372_);
lean_dec(v_pivot_1369_);
v___x_1384_ = lean_array_fswap(v_as_1370_, v_i_1371_, v_hi_1368_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_i_1371_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; lean_object* v_decl_u2081_1387_; lean_object* v_index_1388_; lean_object* v_decl_u2082_1389_; lean_object* v_index_1390_; uint8_t v___x_1391_; 
v___x_1386_ = lean_array_fget_borrowed(v_as_1370_, v_k_1372_);
lean_inc(v___x_1386_);
v_decl_u2081_1387_ = l_Lean_MetavarContext_getDecl(v___x_1367_, v___x_1386_);
v_index_1388_ = lean_ctor_get(v_decl_u2081_1387_, 6);
lean_inc(v_index_1388_);
lean_dec_ref(v_decl_u2081_1387_);
lean_inc(v_pivot_1369_);
v_decl_u2082_1389_ = l_Lean_MetavarContext_getDecl(v___x_1367_, v_pivot_1369_);
v_index_1390_ = lean_ctor_get(v_decl_u2082_1389_, 6);
lean_inc(v_index_1390_);
lean_dec_ref(v_decl_u2082_1389_);
v___x_1391_ = lean_nat_dec_eq(v_index_1388_, v_index_1390_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_lt(v_index_1388_, v_index_1390_);
lean_dec(v_index_1390_);
lean_dec(v_index_1388_);
v___y_1374_ = v___x_1392_;
goto v___jp_1373_;
}
else
{
uint8_t v___x_1393_; 
lean_dec(v_index_1390_);
lean_dec(v_index_1388_);
v___x_1393_ = l_Lean_Name_quickLt(v___x_1386_, v_pivot_1369_);
v___y_1374_ = v___x_1393_;
goto v___jp_1373_;
}
}
v___jp_1373_:
{
if (v___y_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_add(v_k_1372_, v___x_1375_);
lean_dec(v_k_1372_);
v_k_1372_ = v___x_1376_;
goto _start;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_array_fswap(v_as_1370_, v_i_1371_, v_k_1372_);
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_nat_add(v_i_1371_, v___x_1379_);
lean_dec(v_i_1371_);
v___x_1381_ = lean_nat_add(v_k_1372_, v___x_1379_);
lean_dec(v_k_1372_);
v_as_1370_ = v___x_1378_;
v_i_1371_ = v___x_1380_;
v_k_1372_ = v___x_1381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_1394_, lean_object* v_hi_1395_, lean_object* v_pivot_1396_, lean_object* v_as_1397_, lean_object* v_i_1398_, lean_object* v_k_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1394_, v_hi_1395_, v_pivot_1396_, v_as_1397_, v_i_1398_, v_k_1399_);
lean_dec(v_hi_1395_);
lean_dec_ref(v___x_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object* v___x_1401_, lean_object* v_n_1402_, lean_object* v_as_1403_, lean_object* v_lo_1404_, lean_object* v_hi_1405_){
_start:
{
lean_object* v___y_1407_; uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_lt(v_lo_1404_, v_hi_1405_);
if (v___x_1417_ == 0)
{
lean_dec(v_lo_1404_);
return v_as_1403_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_mid_1420_; lean_object* v___y_1422_; lean_object* v___y_1428_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1418_ = lean_nat_add(v_lo_1404_, v_hi_1405_);
v___x_1419_ = lean_unsigned_to_nat(1u);
v_mid_1420_ = lean_nat_shiftr(v___x_1418_, v___x_1419_);
lean_dec(v___x_1418_);
v___x_1433_ = lean_array_fget_borrowed(v_as_1403_, v_mid_1420_);
v___x_1434_ = lean_array_fget_borrowed(v_as_1403_, v_lo_1404_);
lean_inc(v___x_1434_);
lean_inc(v___x_1433_);
v___x_1435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1401_, v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
v___y_1428_ = v_as_1403_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_array_fswap(v_as_1403_, v_lo_1404_, v_mid_1420_);
v___y_1428_ = v___x_1436_;
goto v___jp_1427_;
}
v___jp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_array_fget_borrowed(v___y_1422_, v_mid_1420_);
v___x_1424_ = lean_array_fget_borrowed(v___y_1422_, v_hi_1405_);
lean_inc(v___x_1424_);
lean_inc(v___x_1423_);
v___x_1425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1401_, v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_mid_1420_);
v___y_1407_ = v___y_1422_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_array_fswap(v___y_1422_, v_mid_1420_, v_hi_1405_);
lean_dec(v_mid_1420_);
v___y_1407_ = v___x_1426_;
goto v___jp_1406_;
}
}
v___jp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_array_fget_borrowed(v___y_1428_, v_hi_1405_);
v___x_1430_ = lean_array_fget_borrowed(v___y_1428_, v_lo_1404_);
lean_inc(v___x_1430_);
lean_inc(v___x_1429_);
v___x_1431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1401_, v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
v___y_1422_ = v___y_1428_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_array_fswap(v___y_1428_, v_lo_1404_, v_hi_1405_);
v___y_1422_ = v___x_1432_;
goto v___jp_1421_;
}
}
}
v___jp_1406_:
{
lean_object* v_pivot_1408_; lean_object* v___x_1409_; lean_object* v_fst_1410_; lean_object* v_snd_1411_; uint8_t v___x_1412_; 
v_pivot_1408_ = lean_array_fget(v___y_1407_, v_hi_1405_);
lean_inc_n(v_lo_1404_, 2);
v___x_1409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1401_, v_hi_1405_, v_pivot_1408_, v___y_1407_, v_lo_1404_, v_lo_1404_);
v_fst_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_fst_1410_);
v_snd_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_snd_1411_);
lean_dec_ref(v___x_1409_);
v___x_1412_ = lean_nat_dec_le(v_hi_1405_, v_fst_1410_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1401_, v_n_1402_, v_snd_1411_, v_lo_1404_, v_fst_1410_);
v___x_1414_ = lean_unsigned_to_nat(1u);
v___x_1415_ = lean_nat_add(v_fst_1410_, v___x_1414_);
lean_dec(v_fst_1410_);
v_as_1403_ = v___x_1413_;
v_lo_1404_ = v___x_1415_;
goto _start;
}
else
{
lean_dec(v_fst_1410_);
lean_dec(v_lo_1404_);
return v_snd_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_1437_, lean_object* v_n_1438_, lean_object* v_as_1439_, lean_object* v_lo_1440_, lean_object* v_hi_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1437_, v_n_1438_, v_as_1439_, v_lo_1440_, v_hi_1441_);
lean_dec(v_hi_1441_);
lean_dec(v_n_1438_);
lean_dec_ref(v___x_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object* v_mvarIds_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v_mctx_1447_; lean_object* v___x_1448_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1446_ = lean_st_ref_get(v___y_1444_);
v_mctx_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_mctx_1447_);
lean_dec(v___x_1446_);
v___x_1448_ = lean_array_get_size(v_mvarIds_1443_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_nat_dec_eq(v___x_1448_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; uint8_t v___x_1461_; 
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_sub(v___x_1448_, v___x_1456_);
v___x_1461_ = lean_nat_dec_le(v___x_1454_, v___x_1457_);
if (v___x_1461_ == 0)
{
lean_inc(v___x_1457_);
v___y_1459_ = v___x_1457_;
goto v___jp_1458_;
}
else
{
v___y_1459_ = v___x_1454_;
goto v___jp_1458_;
}
v___jp_1458_:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_nat_dec_le(v___y_1459_, v___x_1457_);
if (v___x_1460_ == 0)
{
lean_dec(v___x_1457_);
lean_inc(v___y_1459_);
v___y_1450_ = v___y_1459_;
v___y_1451_ = v___y_1459_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___y_1459_;
v___y_1451_ = v___x_1457_;
goto v___jp_1449_;
}
}
}
else
{
lean_object* v___x_1462_; 
lean_dec_ref(v_mctx_1447_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_mvarIds_1443_);
return v___x_1462_;
}
v___jp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v_mctx_1447_, v___x_1448_, v_mvarIds_1443_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v_mctx_1447_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object* v_mvarIds_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1463_, v___y_1464_);
lean_dec(v___y_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object* v_k_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v_mctx_1478_; lean_object* v_mvarCounter_1479_; lean_object* v___x_1480_; 
v___x_1477_ = lean_st_ref_get(v___y_1473_);
v_mctx_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc_ref(v_mctx_1478_);
lean_dec(v___x_1477_);
v_mvarCounter_1479_ = lean_ctor_get(v_mctx_1478_, 3);
lean_inc(v_mvarCounter_1479_);
lean_dec_ref(v_mctx_1478_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
v___x_1480_ = lean_apply_9(v_k_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, lean_box(0));
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc_n(v_a_1481_, 2);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = l_Lean_Meta_getMVarsNoDelayed(v_a_1481_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v___x_1484_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1483_, v_mvarCounter_1479_, v___y_1473_);
lean_dec(v_mvarCounter_1479_);
lean_dec(v_a_1483_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_a_1485_, v___y_1473_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_a_1481_);
lean_ctor_set(v___x_1491_, 1, v_a_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1481_);
lean_dec(v_mvarCounter_1479_);
v_a_1496_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1482_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1482_);
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
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_mvarCounter_1479_);
v_a_1504_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1480_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1480_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object* v_k_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* v_k_1523_, lean_object* v_parentTag_1524_, lean_object* v_tagSuffix_1525_, uint8_t v_allowNaturalHoles_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1523_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v_fst_1538_; lean_object* v_snd_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1619_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v_fst_1538_ = lean_ctor_get(v_a_1537_, 0);
v_snd_1539_ = lean_ctor_get(v_a_1537_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_a_1537_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1541_ = v_a_1537_;
v_isShared_1542_ = v_isSharedCheck_1619_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_snd_1539_);
lean_inc(v_fst_1538_);
lean_dec(v_a_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1619_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1575_; lean_object* v_a_1576_; lean_object* v___x_1586_; lean_object* v_a_1588_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_array_get_size(v_snd_1539_);
v___x_1605_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1606_ = lean_nat_dec_lt(v___x_1586_, v___x_1604_);
if (v___x_1606_ == 0)
{
lean_dec(v_snd_1539_);
v_a_1588_ = v___x_1605_;
goto v___jp_1587_;
}
else
{
size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = lean_usize_of_nat(v___x_1604_);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1539_, v___x_1607_, v___x_1608_, v___x_1605_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_snd_1539_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v_a_1588_ = v_a_1610_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_del_object(v___x_1541_);
lean_dec(v_fst_1538_);
lean_dec(v_tagSuffix_1525_);
lean_dec(v_parentTag_1524_);
v_a_1611_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1609_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1609_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
v___jp_1543_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_array_to_list(v___y_1544_);
v___x_1554_ = l_Lean_Elab_Tactic_tagUntaggedGoals(v_parentTag_1524_, v_tagSuffix_1525_, v___x_1553_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1564_; 
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v___x_1554_, 0);
lean_dec(v_unused_1565_);
v___x_1556_ = v___x_1554_;
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v___x_1554_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v___x_1553_);
v___x_1559_ = v___x_1541_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_fst_1538_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1553_);
v___x_1559_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1559_);
v___x_1561_ = v___x_1556_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
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
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v___x_1553_);
lean_del_object(v___x_1541_);
lean_dec(v_fst_1538_);
v_a_1566_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1554_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1554_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1576_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec_ref(v_a_1576_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_dec_ref_known(v___x_1577_, 1);
v___y_1544_ = v___y_1575_;
v___y_1545_ = v_a_1527_;
v___y_1546_ = v_a_1528_;
v___y_1547_ = v_a_1529_;
v___y_1548_ = v_a_1530_;
v___y_1549_ = v_a_1531_;
v___y_1550_ = v_a_1532_;
v___y_1551_ = v_a_1533_;
v___y_1552_ = v_a_1534_;
goto v___jp_1543_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___y_1575_);
lean_del_object(v___x_1541_);
lean_dec(v_fst_1538_);
lean_dec(v_tagSuffix_1525_);
lean_dec(v_parentTag_1524_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
v___jp_1587_:
{
if (v_allowNaturalHoles_1526_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1589_ = lean_array_get_size(v_a_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1591_ = lean_nat_dec_lt(v___x_1586_, v___x_1589_);
if (v___x_1591_ == 0)
{
v___y_1575_ = v_a_1588_;
v_a_1576_ = v___x_1590_;
goto v___jp_1574_;
}
else
{
size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = lean_usize_of_nat(v___x_1589_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1588_, v___x_1592_, v___x_1593_, v___x_1590_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___y_1575_ = v_a_1588_;
v_a_1576_ = v_a_1595_;
goto v___jp_1574_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v_a_1588_);
lean_del_object(v___x_1541_);
lean_dec(v_fst_1538_);
lean_dec(v_tagSuffix_1525_);
lean_dec(v_parentTag_1524_);
v_a_1596_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1594_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
v___y_1544_ = v_a_1588_;
v___y_1545_ = v_a_1527_;
v___y_1546_ = v_a_1528_;
v___y_1547_ = v_a_1529_;
v___y_1548_ = v_a_1530_;
v___y_1549_ = v_a_1531_;
v___y_1550_ = v_a_1532_;
v___y_1551_ = v_a_1533_;
v___y_1552_ = v_a_1534_;
goto v___jp_1543_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_tagSuffix_1525_);
lean_dec(v_parentTag_1524_);
v_a_1620_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1536_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1536_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* v_k_1628_, lean_object* v_parentTag_1629_, lean_object* v_tagSuffix_1630_, lean_object* v_allowNaturalHoles_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1641_; lean_object* v_res_1642_; 
v_allowNaturalHoles_boxed_1641_ = lean_unbox(v_allowNaturalHoles_1631_);
v_res_1642_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1628_, v_parentTag_1629_, v_tagSuffix_1630_, v_allowNaturalHoles_boxed_1641_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object* v_as_1643_, size_t v_i_1644_, size_t v_stop_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1643_, v_i_1644_, v_stop_1645_, v_b_1646_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object* v_as_1657_, lean_object* v_i_1658_, lean_object* v_stop_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
size_t v_i_boxed_1670_; size_t v_stop_boxed_1671_; lean_object* v_res_1672_; 
v_i_boxed_1670_ = lean_unbox_usize(v_i_1658_);
lean_dec(v_i_1658_);
v_stop_boxed_1671_ = lean_unbox_usize(v_stop_1659_);
lean_dec(v_stop_1659_);
v_res_1672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(v_as_1657_, v_i_boxed_1670_, v_stop_boxed_1671_, v_b_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v_as_1657_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object* v_as_1673_, size_t v_i_1674_, size_t v_stop_1675_, lean_object* v_b_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1673_, v_i_1674_, v_stop_1675_, v_b_1676_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_stop_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_i_boxed_1700_; size_t v_stop_boxed_1701_; lean_object* v_res_1702_; 
v_i_boxed_1700_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_stop_boxed_1701_ = lean_unbox_usize(v_stop_1689_);
lean_dec(v_stop_1689_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(v_as_1687_, v_i_boxed_1700_, v_stop_boxed_1701_, v_b_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v_as_1687_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object* v_mvarIds_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1703_, v___y_1705_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object* v_mvarIds_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(v_mvarIds_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object* v___x_1717_, lean_object* v_n_1718_, lean_object* v_as_1719_, lean_object* v_lo_1720_, lean_object* v_hi_1721_, lean_object* v_w_1722_, lean_object* v_hlo_1723_, lean_object* v_hhi_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1717_, v_n_1718_, v_as_1719_, v_lo_1720_, v_hi_1721_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1726_, lean_object* v_n_1727_, lean_object* v_as_1728_, lean_object* v_lo_1729_, lean_object* v_hi_1730_, lean_object* v_w_1731_, lean_object* v_hlo_1732_, lean_object* v_hhi_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(v___x_1726_, v_n_1727_, v_as_1728_, v_lo_1729_, v_hi_1730_, v_w_1731_, v_hlo_1732_, v_hhi_1733_);
lean_dec(v_hi_1730_);
lean_dec(v_n_1727_);
lean_dec_ref(v___x_1726_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1735_, lean_object* v_n_1736_, lean_object* v_lo_1737_, lean_object* v_hi_1738_, lean_object* v_hhi_1739_, lean_object* v_pivot_1740_, lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_k_1743_, lean_object* v_ilo_1744_, lean_object* v_ik_1745_, lean_object* v_w_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1735_, v_hi_1738_, v_pivot_1740_, v_as_1741_, v_i_1742_, v_k_1743_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1748_, lean_object* v_n_1749_, lean_object* v_lo_1750_, lean_object* v_hi_1751_, lean_object* v_hhi_1752_, lean_object* v_pivot_1753_, lean_object* v_as_1754_, lean_object* v_i_1755_, lean_object* v_k_1756_, lean_object* v_ilo_1757_, lean_object* v_ik_1758_, lean_object* v_w_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(v___x_1748_, v_n_1749_, v_lo_1750_, v_hi_1751_, v_hhi_1752_, v_pivot_1753_, v_as_1754_, v_i_1755_, v_k_1756_, v_ilo_1757_, v_ik_1758_, v_w_1759_);
lean_dec(v_hi_1751_);
lean_dec(v_lo_1750_);
lean_dec(v_n_1749_);
lean_dec_ref(v___x_1748_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object* v_k_1761_, lean_object* v_parentTag_1762_, lean_object* v_tagSuffix_1763_, uint8_t v_allowNaturalHoles_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
if (v_allowNaturalHoles_1764_ == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1761_, v_parentTag_1762_, v_tagSuffix_1763_, v_allowNaturalHoles_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
return v___x_1774_;
}
else
{
lean_object* v_declName_x3f_1775_; lean_object* v_macroStack_1776_; uint8_t v_mayPostpone_1777_; uint8_t v_errToSorry_1778_; lean_object* v_autoBoundImplicitContext_1779_; lean_object* v_autoBoundImplicitForbidden_1780_; lean_object* v_sectionVars_1781_; lean_object* v_sectionFVars_1782_; uint8_t v_implicitLambda_1783_; uint8_t v_heedElabAsElim_1784_; uint8_t v_isNoncomputableSection_1785_; uint8_t v_isMetaSection_1786_; uint8_t v_ignoreTCFailures_1787_; uint8_t v_inPattern_1788_; lean_object* v_tacSnap_x3f_1789_; uint8_t v_saveRecAppSyntax_1790_; uint8_t v_holesAsSyntheticOpaque_1791_; lean_object* v_fixedTermElabs_1792_; uint8_t v___y_1794_; 
v_declName_x3f_1775_ = lean_ctor_get(v_a_1767_, 0);
v_macroStack_1776_ = lean_ctor_get(v_a_1767_, 1);
v_mayPostpone_1777_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8);
v_errToSorry_1778_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1779_ = lean_ctor_get(v_a_1767_, 2);
v_autoBoundImplicitForbidden_1780_ = lean_ctor_get(v_a_1767_, 3);
v_sectionVars_1781_ = lean_ctor_get(v_a_1767_, 4);
v_sectionFVars_1782_ = lean_ctor_get(v_a_1767_, 5);
v_implicitLambda_1783_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1784_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1785_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 4);
v_isMetaSection_1786_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1787_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 6);
v_inPattern_1788_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1789_ = lean_ctor_get(v_a_1767_, 6);
v_saveRecAppSyntax_1790_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1791_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*8 + 9);
v_fixedTermElabs_1792_ = lean_ctor_get(v_a_1767_, 7);
if (v_holesAsSyntheticOpaque_1791_ == 0)
{
v___y_1794_ = v_allowNaturalHoles_1764_;
goto v___jp_1793_;
}
else
{
v___y_1794_ = v_holesAsSyntheticOpaque_1791_;
goto v___jp_1793_;
}
v___jp_1793_:
{
lean_object* v___x_1795_; uint8_t v_foApprox_1796_; uint8_t v_ctxApprox_1797_; uint8_t v_quasiPatternApprox_1798_; uint8_t v_constApprox_1799_; uint8_t v_isDefEqStuckEx_1800_; uint8_t v_unificationHints_1801_; uint8_t v_proofIrrelevance_1802_; uint8_t v_offsetCnstrs_1803_; uint8_t v_transparency_1804_; uint8_t v_etaStruct_1805_; uint8_t v_univApprox_1806_; uint8_t v_iota_1807_; uint8_t v_beta_1808_; uint8_t v_proj_1809_; uint8_t v_zeta_1810_; uint8_t v_zetaDelta_1811_; uint8_t v_zetaUnused_1812_; uint8_t v_zetaHave_1813_; uint8_t v_canUnfoldPredicateConfig_1814_; uint8_t v_stringLitToCtor_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1845_; 
v___x_1795_ = l_Lean_Meta_Context_config(v_a_1769_);
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
v_stringLitToCtor_1815_ = lean_ctor_get_uint8(v___x_1795_, 20);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1817_ = v___x_1795_;
v_isShared_1818_ = v_isSharedCheck_1845_;
goto v_resetjp_1816_;
}
else
{
lean_dec(v___x_1795_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1845_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
uint8_t v_trackZetaDelta_1819_; lean_object* v_zetaDeltaSet_1820_; lean_object* v_lctx_1821_; lean_object* v_localInstances_1822_; lean_object* v_defEqCtx_x3f_1823_; lean_object* v_synthPendingDepth_1824_; lean_object* v_customCanUnfoldPredicate_x3f_1825_; uint8_t v_univApprox_1826_; uint8_t v_inTypeClassResolution_1827_; uint8_t v_cacheInferType_1828_; lean_object* v___x_1830_; 
v_trackZetaDelta_1819_ = lean_ctor_get_uint8(v_a_1769_, sizeof(void*)*7);
v_zetaDeltaSet_1820_ = lean_ctor_get(v_a_1769_, 1);
v_lctx_1821_ = lean_ctor_get(v_a_1769_, 2);
v_localInstances_1822_ = lean_ctor_get(v_a_1769_, 3);
v_defEqCtx_x3f_1823_ = lean_ctor_get(v_a_1769_, 4);
v_synthPendingDepth_1824_ = lean_ctor_get(v_a_1769_, 5);
v_customCanUnfoldPredicate_x3f_1825_ = lean_ctor_get(v_a_1769_, 6);
v_univApprox_1826_ = lean_ctor_get_uint8(v_a_1769_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1827_ = lean_ctor_get_uint8(v_a_1769_, sizeof(void*)*7 + 2);
v_cacheInferType_1828_ = lean_ctor_get_uint8(v_a_1769_, sizeof(void*)*7 + 3);
if (v_isShared_1818_ == 0)
{
v___x_1830_ = v___x_1817_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 0, v_foApprox_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 1, v_ctxApprox_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 2, v_quasiPatternApprox_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 3, v_constApprox_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 4, v_isDefEqStuckEx_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 5, v_unificationHints_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 6, v_proofIrrelevance_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 8, v_offsetCnstrs_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 9, v_transparency_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 10, v_etaStruct_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 11, v_univApprox_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 12, v_iota_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 13, v_beta_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 14, v_proj_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 15, v_zeta_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 16, v_zetaDelta_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 17, v_zetaUnused_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 18, v_zetaHave_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 19, v_canUnfoldPredicateConfig_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, 20, v_stringLitToCtor_1815_);
v___x_1830_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
uint64_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_ctor_set_uint8(v___x_1830_, 7, v_allowNaturalHoles_1764_);
v___x_1831_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1830_);
lean_inc_ref(v_fixedTermElabs_1792_);
lean_inc(v_tacSnap_x3f_1789_);
lean_inc(v_sectionFVars_1782_);
lean_inc(v_sectionVars_1781_);
lean_inc_ref(v_autoBoundImplicitForbidden_1780_);
lean_inc(v_autoBoundImplicitContext_1779_);
lean_inc(v_macroStack_1776_);
lean_inc(v_declName_x3f_1775_);
v___x_1832_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_1832_, 0, v_declName_x3f_1775_);
lean_ctor_set(v___x_1832_, 1, v_macroStack_1776_);
lean_ctor_set(v___x_1832_, 2, v_autoBoundImplicitContext_1779_);
lean_ctor_set(v___x_1832_, 3, v_autoBoundImplicitForbidden_1780_);
lean_ctor_set(v___x_1832_, 4, v_sectionVars_1781_);
lean_ctor_set(v___x_1832_, 5, v_sectionFVars_1782_);
lean_ctor_set(v___x_1832_, 6, v_tacSnap_x3f_1789_);
lean_ctor_set(v___x_1832_, 7, v_fixedTermElabs_1792_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8, v_mayPostpone_1777_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 1, v_errToSorry_1778_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 2, v_implicitLambda_1783_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 3, v_heedElabAsElim_1784_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1785_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 5, v_isMetaSection_1786_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1787_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 7, v_inPattern_1788_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1790_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*8 + 9, v___y_1794_);
v___x_1833_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1833_, 0, v___x_1830_);
lean_ctor_set_uint64(v___x_1833_, sizeof(void*)*1, v___x_1831_);
lean_inc(v_customCanUnfoldPredicate_x3f_1825_);
lean_inc(v_synthPendingDepth_1824_);
lean_inc(v_defEqCtx_x3f_1823_);
lean_inc_ref(v_localInstances_1822_);
lean_inc_ref(v_lctx_1821_);
lean_inc(v_zetaDeltaSet_1820_);
v___x_1834_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v_zetaDeltaSet_1820_);
lean_ctor_set(v___x_1834_, 2, v_lctx_1821_);
lean_ctor_set(v___x_1834_, 3, v_localInstances_1822_);
lean_ctor_set(v___x_1834_, 4, v_defEqCtx_x3f_1823_);
lean_ctor_set(v___x_1834_, 5, v_synthPendingDepth_1824_);
lean_ctor_set(v___x_1834_, 6, v_customCanUnfoldPredicate_x3f_1825_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*7, v_trackZetaDelta_1819_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*7 + 1, v_univApprox_1826_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1827_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*7 + 3, v_cacheInferType_1828_);
v___x_1835_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1761_, v_parentTag_1762_, v_tagSuffix_1763_, v_allowNaturalHoles_1764_, v_a_1765_, v_a_1766_, v___x_1832_, v_a_1768_, v___x_1834_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec_ref_known(v___x_1834_, 7);
lean_dec_ref_known(v___x_1832_, 8);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
return v___x_1835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object* v_k_1846_, lean_object* v_parentTag_1847_, lean_object* v_tagSuffix_1848_, lean_object* v_allowNaturalHoles_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1859_; lean_object* v_res_1860_; 
v_allowNaturalHoles_boxed_1859_ = lean_unbox(v_allowNaturalHoles_1849_);
v_res_1860_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v_k_1846_, v_parentTag_1847_, v_tagSuffix_1848_, v_allowNaturalHoles_boxed_1859_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* v_stx_1861_, lean_object* v_expectedType_x3f_1862_, lean_object* v_tagSuffix_1863_, uint8_t v_allowNaturalHoles_1864_, lean_object* v_parentTag_x3f_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_a_1876_; 
if (lean_obj_tag(v_parentTag_x3f_1865_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Elab_Tactic_getMainTag___redArg(v_a_1867_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v_a_1876_ = v_a_1882_;
goto v___jp_1875_;
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_tagSuffix_1863_);
lean_dec(v_expectedType_x3f_1862_);
lean_dec(v_stx_1861_);
v_a_1883_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1881_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_val_1891_; 
v_val_1891_ = lean_ctor_get(v_parentTag_x3f_1865_, 0);
lean_inc(v_val_1891_);
lean_dec_ref_known(v_parentTag_x3f_1865_, 1);
v_a_1876_ = v_val_1891_;
goto v___jp_1875_;
}
v___jp_1875_:
{
uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = 0;
v___x_1878_ = lean_box(v___x_1877_);
v___x_1879_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(v___x_1879_, 0, v_stx_1861_);
lean_closure_set(v___x_1879_, 1, v_expectedType_x3f_1862_);
lean_closure_set(v___x_1879_, 2, v___x_1878_);
v___x_1880_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_1879_, v_a_1876_, v_tagSuffix_1863_, v_allowNaturalHoles_1864_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* v_stx_1892_, lean_object* v_expectedType_x3f_1893_, lean_object* v_tagSuffix_1894_, lean_object* v_allowNaturalHoles_1895_, lean_object* v_parentTag_x3f_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1906_; lean_object* v_res_1907_; 
v_allowNaturalHoles_boxed_1906_ = lean_unbox(v_allowNaturalHoles_1895_);
v_res_1907_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_1892_, v_expectedType_x3f_1893_, v_tagSuffix_1894_, v_allowNaturalHoles_boxed_1906_, v_parentTag_x3f_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1907_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object* v_a_1908_, lean_object* v_x_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Lean_instBEqMVarId_beq(v_x_1909_, v_a_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object* v_a_1911_, lean_object* v_x_1912_){
_start:
{
uint8_t v_res_1913_; lean_object* v_r_1914_; 
v_res_1913_ = l_Lean_Elab_Tactic_refineCore___lam__0(v_a_1911_, v_x_1912_);
lean_dec(v_x_1912_);
lean_dec(v_a_1911_);
v_r_1914_ = lean_box(v_res_1913_);
return v_r_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v_ks_1919_; lean_object* v_vs_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1944_; 
v_ks_1919_ = lean_ctor_get(v_x_1915_, 0);
v_vs_1920_ = lean_ctor_get(v_x_1915_, 1);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_x_1915_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1922_ = v_x_1915_;
v_isShared_1923_ = v_isSharedCheck_1944_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_vs_1920_);
lean_inc(v_ks_1919_);
lean_dec(v_x_1915_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1944_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = lean_array_get_size(v_ks_1919_);
v___x_1925_ = lean_nat_dec_lt(v_x_1916_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
lean_dec(v_x_1916_);
v___x_1926_ = lean_array_push(v_ks_1919_, v_x_1917_);
v___x_1927_ = lean_array_push(v_vs_1920_, v_x_1918_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1927_);
lean_ctor_set(v___x_1922_, 0, v___x_1926_);
v___x_1929_ = v___x_1922_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
else
{
lean_object* v_k_x27_1931_; uint8_t v___x_1932_; 
v_k_x27_1931_ = lean_array_fget_borrowed(v_ks_1919_, v_x_1916_);
v___x_1932_ = l_Lean_instBEqMVarId_beq(v_x_1917_, v_k_x27_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1934_; 
if (v_isShared_1923_ == 0)
{
v___x_1934_ = v___x_1922_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_ks_1919_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_vs_1920_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v_x_1916_, v___x_1935_);
lean_dec(v_x_1916_);
v_x_1915_ = v___x_1934_;
v_x_1916_ = v___x_1936_;
goto _start;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1939_ = lean_array_fset(v_ks_1919_, v_x_1916_, v_x_1917_);
v___x_1940_ = lean_array_fset(v_vs_1920_, v_x_1916_, v_x_1918_);
lean_dec(v_x_1916_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1940_);
lean_ctor_set(v___x_1922_, 0, v___x_1939_);
v___x_1942_ = v___x_1922_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1940_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_1945_, lean_object* v_k_1946_, lean_object* v_v_1947_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_1945_, v___x_1948_, v_k_1946_, v_v_1947_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1951_, size_t v_x_1952_, size_t v_x_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
if (lean_obj_tag(v_x_1951_) == 0)
{
lean_object* v_es_1956_; size_t v___x_1957_; size_t v___x_1958_; lean_object* v_j_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v_es_1956_ = lean_ctor_get(v_x_1951_, 0);
v___x_1957_ = ((size_t)31ULL);
v___x_1958_ = lean_usize_land(v_x_1952_, v___x_1957_);
v_j_1959_ = lean_usize_to_nat(v___x_1958_);
v___x_1960_ = lean_array_get_size(v_es_1956_);
v___x_1961_ = lean_nat_dec_lt(v_j_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_dec(v_j_1959_);
lean_dec(v_x_1955_);
lean_dec(v_x_1954_);
return v_x_1951_;
}
else
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2000_; 
lean_inc_ref(v_es_1956_);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1951_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_x_1951_, 0);
lean_dec(v_unused_2001_);
v___x_1963_ = v_x_1951_;
v_isShared_1964_ = v_isSharedCheck_2000_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v_x_1951_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2000_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_v_1965_; lean_object* v___x_1966_; lean_object* v_xs_x27_1967_; lean_object* v___y_1969_; 
v_v_1965_ = lean_array_fget(v_es_1956_, v_j_1959_);
v___x_1966_ = lean_box(0);
v_xs_x27_1967_ = lean_array_fset(v_es_1956_, v_j_1959_, v___x_1966_);
switch(lean_obj_tag(v_v_1965_))
{
case 0:
{
lean_object* v_key_1974_; lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1985_; 
v_key_1974_ = lean_ctor_get(v_v_1965_, 0);
v_val_1975_ = lean_ctor_get(v_v_1965_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_v_1965_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1977_ = v_v_1965_;
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_inc(v_key_1974_);
lean_dec(v_v_1965_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_instBEqMVarId_beq(v_x_1954_, v_key_1974_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_del_object(v___x_1977_);
v___x_1980_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1974_, v_val_1975_, v_x_1954_, v_x_1955_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
v___y_1969_ = v___x_1981_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_1983_; 
lean_dec(v_val_1975_);
lean_dec(v_key_1974_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v_x_1955_);
lean_ctor_set(v___x_1977_, 0, v_x_1954_);
v___x_1983_ = v___x_1977_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_x_1954_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_x_1955_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
v___y_1969_ = v___x_1983_;
goto v___jp_1968_;
}
}
}
}
case 1:
{
lean_object* v_node_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1998_; 
v_node_1986_ = lean_ctor_get(v_v_1965_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_v_1965_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1988_ = v_v_1965_;
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_node_1986_);
lean_dec(v_v_1965_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1990_ = ((size_t)5ULL);
v___x_1991_ = lean_usize_shift_right(v_x_1952_, v___x_1990_);
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_x_1953_, v___x_1992_);
v___x_1994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_node_1986_, v___x_1991_, v___x_1993_, v_x_1954_, v_x_1955_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1994_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
v___y_1969_ = v___x_1996_;
goto v___jp_1968_;
}
}
}
default: 
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_x_1954_);
lean_ctor_set(v___x_1999_, 1, v_x_1955_);
v___y_1969_ = v___x_1999_;
goto v___jp_1968_;
}
}
v___jp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_array_fset(v_xs_x27_1967_, v_j_1959_, v___y_1969_);
lean_dec(v_j_1959_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1970_);
v___x_1972_ = v___x_1963_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_ks_2002_; lean_object* v_vs_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2021_; 
v_ks_2002_ = lean_ctor_get(v_x_1951_, 0);
v_vs_2003_ = lean_ctor_get(v_x_1951_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_x_1951_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2005_ = v_x_1951_;
v_isShared_2006_ = v_isSharedCheck_2021_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_vs_2003_);
lean_inc(v_ks_2002_);
lean_dec(v_x_1951_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2021_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_ks_2002_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_vs_2003_);
v___x_2008_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v_newNode_2009_; size_t v___x_2010_; uint8_t v___x_2011_; 
v_newNode_2009_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_2008_, v_x_1954_, v_x_1955_);
v___x_2010_ = ((size_t)7ULL);
v___x_2011_ = lean_usize_dec_le(v___x_2010_, v_x_1953_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2009_);
v___x_2013_ = lean_unsigned_to_nat(4u);
v___x_2014_ = lean_nat_dec_lt(v___x_2012_, v___x_2013_);
lean_dec(v___x_2012_);
if (v___x_2014_ == 0)
{
lean_object* v_ks_2015_; lean_object* v_vs_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_ks_2015_ = lean_ctor_get(v_newNode_2009_, 0);
lean_inc_ref(v_ks_2015_);
v_vs_2016_ = lean_ctor_get(v_newNode_2009_, 1);
lean_inc_ref(v_vs_2016_);
lean_dec_ref(v_newNode_2009_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2019_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1953_, v_ks_2015_, v_vs_2016_, v___x_2017_, v___x_2018_);
lean_dec_ref(v_vs_2016_);
lean_dec_ref(v_ks_2015_);
return v___x_2019_;
}
else
{
return v_newNode_2009_;
}
}
else
{
return v_newNode_2009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_2022_, lean_object* v_keys_2023_, lean_object* v_vals_2024_, lean_object* v_i_2025_, lean_object* v_entries_2026_){
_start:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_array_get_size(v_keys_2023_);
v___x_2028_ = lean_nat_dec_lt(v_i_2025_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_dec(v_i_2025_);
return v_entries_2026_;
}
else
{
lean_object* v_k_2029_; lean_object* v_v_2030_; uint64_t v___x_2031_; size_t v_h_2032_; size_t v___x_2033_; lean_object* v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; size_t v___x_2037_; size_t v_h_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_k_2029_ = lean_array_fget_borrowed(v_keys_2023_, v_i_2025_);
v_v_2030_ = lean_array_fget_borrowed(v_vals_2024_, v_i_2025_);
v___x_2031_ = l_Lean_instHashableMVarId_hash(v_k_2029_);
v_h_2032_ = lean_uint64_to_usize(v___x_2031_);
v___x_2033_ = ((size_t)5ULL);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_sub(v_depth_2022_, v___x_2035_);
v___x_2037_ = lean_usize_mul(v___x_2033_, v___x_2036_);
v_h_2038_ = lean_usize_shift_right(v_h_2032_, v___x_2037_);
v___x_2039_ = lean_nat_add(v_i_2025_, v___x_2034_);
lean_dec(v_i_2025_);
lean_inc(v_v_2030_);
lean_inc(v_k_2029_);
v___x_2040_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_entries_2026_, v_h_2038_, v_depth_2022_, v_k_2029_, v_v_2030_);
v_i_2025_ = v___x_2039_;
v_entries_2026_ = v___x_2040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_2042_, lean_object* v_keys_2043_, lean_object* v_vals_2044_, lean_object* v_i_2045_, lean_object* v_entries_2046_){
_start:
{
size_t v_depth_boxed_2047_; lean_object* v_res_2048_; 
v_depth_boxed_2047_ = lean_unbox_usize(v_depth_2042_);
lean_dec(v_depth_2042_);
v_res_2048_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_2047_, v_keys_2043_, v_vals_2044_, v_i_2045_, v_entries_2046_);
lean_dec_ref(v_vals_2044_);
lean_dec_ref(v_keys_2043_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
size_t v_x_3343__boxed_2054_; size_t v_x_3344__boxed_2055_; lean_object* v_res_2056_; 
v_x_3343__boxed_2054_ = lean_unbox_usize(v_x_2050_);
lean_dec(v_x_2050_);
v_x_3344__boxed_2055_ = lean_unbox_usize(v_x_2051_);
lean_dec(v_x_2051_);
v_res_2056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2049_, v_x_3343__boxed_2054_, v_x_3344__boxed_2055_, v_x_2052_, v_x_2053_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_){
_start:
{
uint64_t v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = l_Lean_instHashableMVarId_hash(v_x_2058_);
v___x_2061_ = lean_uint64_to_usize(v___x_2060_);
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2057_, v___x_2061_, v___x_2062_, v_x_2058_, v_x_2059_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object* v_mvarId_2064_, lean_object* v_val_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; lean_object* v_mctx_2069_; lean_object* v_cache_2070_; lean_object* v_zetaDeltaFVarIds_2071_; lean_object* v_postponed_2072_; lean_object* v_diag_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2102_; 
v___x_2068_ = lean_st_ref_take(v___y_2066_);
v_mctx_2069_ = lean_ctor_get(v___x_2068_, 0);
v_cache_2070_ = lean_ctor_get(v___x_2068_, 1);
v_zetaDeltaFVarIds_2071_ = lean_ctor_get(v___x_2068_, 2);
v_postponed_2072_ = lean_ctor_get(v___x_2068_, 3);
v_diag_2073_ = lean_ctor_get(v___x_2068_, 4);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2075_ = v___x_2068_;
v_isShared_2076_ = v_isSharedCheck_2102_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_diag_2073_);
lean_inc(v_postponed_2072_);
lean_inc(v_zetaDeltaFVarIds_2071_);
lean_inc(v_cache_2070_);
lean_inc(v_mctx_2069_);
lean_dec(v___x_2068_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2102_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_depth_2077_; lean_object* v_levelAssignDepth_2078_; lean_object* v_lmvarCounter_2079_; lean_object* v_mvarCounter_2080_; lean_object* v_lDecls_2081_; lean_object* v_decls_2082_; lean_object* v_userNames_2083_; lean_object* v_lAssignment_2084_; lean_object* v_eAssignment_2085_; lean_object* v_dAssignment_2086_; lean_object* v_instanceTypedMVars_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2101_; 
v_depth_2077_ = lean_ctor_get(v_mctx_2069_, 0);
v_levelAssignDepth_2078_ = lean_ctor_get(v_mctx_2069_, 1);
v_lmvarCounter_2079_ = lean_ctor_get(v_mctx_2069_, 2);
v_mvarCounter_2080_ = lean_ctor_get(v_mctx_2069_, 3);
v_lDecls_2081_ = lean_ctor_get(v_mctx_2069_, 4);
v_decls_2082_ = lean_ctor_get(v_mctx_2069_, 5);
v_userNames_2083_ = lean_ctor_get(v_mctx_2069_, 6);
v_lAssignment_2084_ = lean_ctor_get(v_mctx_2069_, 7);
v_eAssignment_2085_ = lean_ctor_get(v_mctx_2069_, 8);
v_dAssignment_2086_ = lean_ctor_get(v_mctx_2069_, 9);
v_instanceTypedMVars_2087_ = lean_ctor_get(v_mctx_2069_, 10);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_mctx_2069_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2089_ = v_mctx_2069_;
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_instanceTypedMVars_2087_);
lean_inc(v_dAssignment_2086_);
lean_inc(v_eAssignment_2085_);
lean_inc(v_lAssignment_2084_);
lean_inc(v_userNames_2083_);
lean_inc(v_decls_2082_);
lean_inc(v_lDecls_2081_);
lean_inc(v_mvarCounter_2080_);
lean_inc(v_lmvarCounter_2079_);
lean_inc(v_levelAssignDepth_2078_);
lean_inc(v_depth_2077_);
lean_dec(v_mctx_2069_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_eAssignment_2085_, v_mvarId_2064_, v_val_2065_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 8, v___x_2092_);
v___x_2094_ = v___x_2089_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_depth_2077_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_levelAssignDepth_2078_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_lmvarCounter_2079_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_mvarCounter_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_lDecls_2081_);
lean_ctor_set(v_reuseFailAlloc_2100_, 5, v_decls_2082_);
lean_ctor_set(v_reuseFailAlloc_2100_, 6, v_userNames_2083_);
lean_ctor_set(v_reuseFailAlloc_2100_, 7, v_lAssignment_2084_);
lean_ctor_set(v_reuseFailAlloc_2100_, 8, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2100_, 9, v_dAssignment_2086_);
lean_ctor_set(v_reuseFailAlloc_2100_, 10, v_instanceTypedMVars_2087_);
v___x_2094_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2094_);
v___x_2096_ = v___x_2075_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_cache_2070_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_zetaDeltaFVarIds_2071_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_postponed_2072_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v_diag_2073_);
v___x_2096_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_st_ref_put(v___y_2066_, v___x_2096_);
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
size_t v_x_3893__boxed_2358_; size_t v_x_3894__boxed_2359_; lean_object* v_res_2360_; 
v_x_3893__boxed_2358_ = lean_unbox_usize(v_x_2354_);
lean_dec(v_x_2354_);
v_x_3894__boxed_2359_ = lean_unbox_usize(v_x_2355_);
lean_dec(v_x_2355_);
v_res_2360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(v_00_u03b2_2352_, v_x_2353_, v_x_3893__boxed_2358_, v_x_3894__boxed_2359_, v_x_2356_, v_x_2357_);
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
lean_object* v_toCold_2845_; lean_object* v_currRecDepth_2846_; lean_object* v_ref_2847_; uint16_t v_optionFlags_2848_; uint8_t v_suppressElabErrors_2849_; uint8_t v_checkDeprecated_2850_; uint8_t v_isRecordingDeps_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___f_2855_; lean_object* v_ref_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_toCold_2845_ = lean_ctor_get(v_a_2842_, 0);
v_currRecDepth_2846_ = lean_ctor_get(v_a_2842_, 1);
v_ref_2847_ = lean_ctor_get(v_a_2842_, 2);
v_optionFlags_2848_ = lean_ctor_get_uint16(v_a_2842_, sizeof(void*)*3);
v_suppressElabErrors_2849_ = lean_ctor_get_uint8(v_a_2842_, sizeof(void*)*3 + 2);
v_checkDeprecated_2850_ = lean_ctor_get_uint8(v_a_2842_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2851_ = lean_ctor_get_uint8(v_a_2842_, sizeof(void*)*3 + 4);
v___x_2852_ = 0;
v___x_2853_ = lean_box(v___x_2852_);
lean_inc(v_id_2835_);
v___x_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_2854_, 0, v_id_2835_);
lean_closure_set(v___x_2854_, 1, v___x_2853_);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2855_, 0, v___x_2854_);
v_ref_2856_ = l_Lean_replaceRef(v_id_2835_, v_ref_2847_);
lean_dec(v_id_2835_);
lean_inc(v_currRecDepth_2846_);
lean_inc_ref(v_toCold_2845_);
v___x_2857_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2857_, 0, v_toCold_2845_);
lean_ctor_set(v___x_2857_, 1, v_currRecDepth_2846_);
lean_ctor_set(v___x_2857_, 2, v_ref_2856_);
lean_ctor_set_uint16(v___x_2857_, sizeof(void*)*3, v_optionFlags_2848_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*3 + 2, v_suppressElabErrors_2849_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*3 + 3, v_checkDeprecated_2850_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*3 + 4, v_isRecordingDeps_2851_);
v___x_2858_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2855_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v___x_2857_, v_a_2843_);
lean_dec_ref_known(v___x_2857_, 3);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object* v_id_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Elab_Tactic_getFVarId(v_id_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t v_sz_2870_, size_t v_i_2871_, lean_object* v_bs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_usize_dec_lt(v_i_2871_, v_sz_2870_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_bs_2872_);
return v___x_2883_;
}
else
{
lean_object* v_v_2884_; lean_object* v___x_2885_; lean_object* v_bs_x27_2886_; lean_object* v___x_2887_; 
v_v_2884_ = lean_array_uget(v_bs_2872_, v_i_2871_);
v___x_2885_ = lean_unsigned_to_nat(0u);
v_bs_x27_2886_ = lean_array_uset(v_bs_2872_, v_i_2871_, v___x_2885_);
v___x_2887_ = l_Lean_Elab_Tactic_getFVarId(v_v_2884_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; size_t v___x_2889_; size_t v___x_2890_; lean_object* v___x_2891_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2871_, v___x_2889_);
v___x_2891_ = lean_array_uset(v_bs_x27_2886_, v_i_2871_, v_a_2888_);
v_i_2871_ = v___x_2890_;
v_bs_2872_ = v___x_2891_;
goto _start;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v_bs_x27_2886_);
v_a_2893_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2887_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2887_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object* v_sz_2901_, lean_object* v_i_2902_, lean_object* v_bs_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
size_t v_sz_boxed_2913_; size_t v_i_boxed_2914_; lean_object* v_res_2915_; 
v_sz_boxed_2913_ = lean_unbox_usize(v_sz_2901_);
lean_dec(v_sz_2901_);
v_i_boxed_2914_ = lean_unbox_usize(v_i_2902_);
lean_dec(v_i_2902_);
v_res_2915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(v_sz_boxed_2913_, v_i_boxed_2914_, v_bs_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* v_ids_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
size_t v_sz_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_sz_2928_ = lean_array_size(v_ids_2918_);
v___x_2929_ = lean_box_usize(v_sz_2928_);
v___x_2930_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1));
v___x_2931_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed), 12, 3);
lean_closure_set(v___x_2931_, 0, v___x_2929_);
lean_closure_set(v___x_2931_, 1, v___x_2930_);
lean_closure_set(v___x_2931_, 2, v_ids_2918_);
v___x_2932_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2931_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object* v_ids_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_Tactic_getFVarIds(v_ids_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object* v_tac_2944_, lean_object* v_e_2945_, uint8_t v___x_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_val_2957_; lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Elab_Tactic_elabTermForApply(v_e_2945_, v___x_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v_a_2984_; uint8_t v___x_2985_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_2982_, v___y_2952_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = l_Lean_Expr_isMVar(v_a_2984_);
if (v___x_2985_ == 0)
{
v_val_2957_ = v_a_2984_;
goto v___jp_2956_;
}
else
{
uint8_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = 0;
v___x_2987_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2986_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v___x_2988_; lean_object* v_a_2989_; 
lean_dec_ref_known(v___x_2987_, 1);
v___x_2988_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_2984_, v___y_2952_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___x_2988_);
v_val_2957_ = v_a_2989_;
goto v___jp_2956_;
}
else
{
lean_dec(v_a_2984_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_tac_2944_);
return v___x_2987_;
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_tac_2944_);
v_a_2990_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2981_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2981_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
v___jp_2956_:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2948_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
v___x_2960_ = lean_apply_7(v_tac_2944_, v_a_2959_, v_val_2957_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, lean_box(0));
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = 0;
v___x_2963_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2962_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; 
lean_dec_ref_known(v___x_2963_, 1);
v___x_2964_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_2961_, v___y_2948_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v___x_2964_;
}
else
{
lean_dec(v_a_2961_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v___x_2963_;
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
v_a_2965_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2960_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2960_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_val_2957_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_tac_2944_);
v_a_2973_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2958_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2958_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object* v_tac_2998_, lean_object* v_e_2999_, lean_object* v___x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
uint8_t v___x_920__boxed_3010_; lean_object* v_res_3011_; 
v___x_920__boxed_3010_ = lean_unbox(v___x_3000_);
v_res_3011_ = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(v_tac_2998_, v_e_2999_, v___x_920__boxed_3010_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* v_tac_3012_, lean_object* v_e_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; 
v___x_3023_ = 1;
v___x_3024_ = lean_box(v___x_3023_);
v___f_3025_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3025_, 0, v_tac_3012_);
lean_closure_set(v___f_3025_, 1, v_e_3013_);
lean_closure_set(v___f_3025_, 2, v___x_3024_);
v___x_3026_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3025_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object* v_tac_3027_, lean_object* v_e_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v_tac_3027_, v_e_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t v___x_3039_, lean_object* v_g_3040_, lean_object* v_e_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
uint8_t v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3047_ = 0;
v___x_3048_ = 0;
v___x_3049_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3049_, 0, v___x_3047_);
lean_ctor_set_uint8(v___x_3049_, 1, v___x_3039_);
lean_ctor_set_uint8(v___x_3049_, 2, v___x_3048_);
lean_ctor_set_uint8(v___x_3049_, 3, v___x_3039_);
v___x_3050_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
lean_inc_ref(v_e_3041_);
v___x_3051_ = l_Lean_MessageData_ofExpr(v_e_3041_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___x_3050_);
v___x_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
v___x_3055_ = l_Lean_MVarId_apply(v_g_3040_, v_e_3041_, v___x_3049_, v___x_3054_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object* v___x_3056_, lean_object* v_g_3057_, lean_object* v_e_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v___x_160__boxed_3064_; lean_object* v_res_3065_; 
v___x_160__boxed_3064_ = lean_unbox(v___x_3056_);
v_res_3065_ = l_Lean_Elab_Tactic_evalApply___lam__0(v___x_160__boxed_3064_, v_g_3057_, v_e_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* v_stx_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
lean_inc(v_stx_3072_);
v___x_3083_ = l_Lean_Syntax_isOfKind(v_stx_3072_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
lean_dec(v_stx_3072_);
v___x_3084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3085_ = lean_box(v___x_3083_);
v___f_3086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3086_, 0, v___x_3085_);
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = l_Lean_Syntax_getArg(v_stx_3072_, v___x_3087_);
lean_dec(v_stx_3072_);
v___x_3089_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v___f_3086_, v___x_3088_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object* v_stx_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Elab_Tactic_evalApply(v_stx_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3108_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3109_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
v___x_3110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3111_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___boxed), 10, 0);
v___x_3112_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3108_, v___x_3109_, v___x_3110_, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6));
v___x_3143_ = l_Lean_addBuiltinDeclarationRanges(v___x_3141_, v___x_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object* v_a_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
return v_res_3145_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_3148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(lean_object* v_00_u03b1_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(v_00_u03b1_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(lean_object* v_msg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_ref_3174_; lean_object* v___x_3175_; lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3184_; 
v_ref_3174_ = lean_ctor_get(v___y_3171_, 2);
v___x_3175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
lean_inc(v_ref_3174_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v_ref_3174_);
lean_ctor_set(v___x_3180_, 1, v_a_3176_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set_tag(v___x_3178_, 1);
lean_ctor_set(v___x_3178_, 0, v___x_3180_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v_msg_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
return v_res_3191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__1));
v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(lean_object* v___x_3196_, lean_object* v_ctor_3197_, lean_object* v_args_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__0));
v___x_3225_ = lean_string_dec_eq(v_ctor_3197_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v___x_3226_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3227_ = lean_array_get_size(v_args_3198_);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_dec_eq(v___x_3227_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
v___x_3230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2);
v___x_3231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v___x_3230_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
else
{
goto v___jp_3204_;
}
}
v___jp_3204_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = lean_array_get_borrowed(v___x_3196_, v_args_3198_, v___x_3205_);
lean_inc(v___x_3206_);
v___x_3207_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_3206_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
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
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
v_a_3216_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3207_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3207_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed(lean_object* v___x_3240_, lean_object* v_ctor_3241_, lean_object* v_args_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(v___x_3240_, v_ctor_3241_, v_args_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v_args_3242_);
lean_dec_ref(v_ctor_3241_);
lean_dec_ref(v___x_3240_);
return v_res_3248_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___f_3250_; 
v___x_3249_ = l_Lean_instInhabitedExpr;
v___f_3250_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3250_, 0, v___x_3249_);
return v___f_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___f_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___f_3263_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0);
v___x_3264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3265_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_3264_, v___f_3263_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___boxed(lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(lean_object* v_00_u03b1_3273_, lean_object* v_msg_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v_msg_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_msg_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(v_00_u03b1_3281_, v_msg_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3288_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = lean_box(0);
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3292_ = l_Lean_Expr_const___override(v___x_3291_, v___x_3290_);
return v___x_3292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2);
v___x_3296_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__0));
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig(void){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_box(0);
v___x_3300_ = l_Lean_Elab_abortTermExceptionId;
v___x_3301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Lean_Expr_hasMVar(v_e_3307_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_e_3307_);
return v___x_3311_;
}
else
{
lean_object* v___x_3312_; lean_object* v_mctx_3313_; lean_object* v___x_3314_; lean_object* v_fst_3315_; lean_object* v_snd_3316_; lean_object* v___x_3317_; lean_object* v_cache_3318_; lean_object* v_zetaDeltaFVarIds_3319_; lean_object* v_postponed_3320_; lean_object* v_diag_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3330_; 
v___x_3312_ = lean_st_ref_get(v___y_3308_);
v_mctx_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_ref(v_mctx_3313_);
lean_dec(v___x_3312_);
v___x_3314_ = l_Lean_instantiateMVarsCore(v_mctx_3313_, v_e_3307_);
v_fst_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_fst_3315_);
v_snd_3316_ = lean_ctor_get(v___x_3314_, 1);
lean_inc(v_snd_3316_);
lean_dec_ref(v___x_3314_);
v___x_3317_ = lean_st_ref_take(v___y_3308_);
v_cache_3318_ = lean_ctor_get(v___x_3317_, 1);
v_zetaDeltaFVarIds_3319_ = lean_ctor_get(v___x_3317_, 2);
v_postponed_3320_ = lean_ctor_get(v___x_3317_, 3);
v_diag_3321_ = lean_ctor_get(v___x_3317_, 4);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; 
v_unused_3331_ = lean_ctor_get(v___x_3317_, 0);
lean_dec(v_unused_3331_);
v___x_3323_ = v___x_3317_;
v_isShared_3324_ = v_isSharedCheck_3330_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_diag_3321_);
lean_inc(v_postponed_3320_);
lean_inc(v_zetaDeltaFVarIds_3319_);
lean_inc(v_cache_3318_);
lean_dec(v___x_3317_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3330_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v_snd_3316_);
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_snd_3316_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_cache_3318_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_zetaDeltaFVarIds_3319_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_postponed_3320_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_diag_3321_);
v___x_3326_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = lean_st_ref_put(v___y_3308_, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_fst_3315_);
return v___x_3328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3332_, v___y_3333_);
lean_dec(v___y_3333_);
return v_res_3335_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_opts_3336_, lean_object* v_opt_3337_){
_start:
{
lean_object* v_name_3338_; lean_object* v_defValue_3339_; lean_object* v_map_3340_; lean_object* v___x_3341_; 
v_name_3338_ = lean_ctor_get(v_opt_3337_, 0);
v_defValue_3339_ = lean_ctor_get(v_opt_3337_, 1);
v_map_3340_ = lean_ctor_get(v_opts_3336_, 0);
v___x_3341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3340_, v_name_3338_);
if (lean_obj_tag(v___x_3341_) == 0)
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_unbox(v_defValue_3339_);
return v___x_3342_;
}
else
{
lean_object* v_val_3343_; 
v_val_3343_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3341_, 1);
if (lean_obj_tag(v_val_3343_) == 1)
{
uint8_t v_v_3344_; 
v_v_3344_ = lean_ctor_get_uint8(v_val_3343_, 0);
lean_dec_ref_known(v_val_3343_, 0);
return v_v_3344_;
}
else
{
uint8_t v___x_3345_; 
lean_dec(v_val_3343_);
v___x_3345_ = lean_unbox(v_defValue_3339_);
return v___x_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_3346_, lean_object* v_opt_3347_){
_start:
{
uint8_t v_res_3348_; lean_object* v_r_3349_; 
v_res_3348_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_3346_, v_opt_3347_);
lean_dec_ref(v_opt_3347_);
lean_dec_ref(v_opts_3346_);
v_r_3349_ = lean_box(v_res_3348_);
return v_r_3349_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_box(1);
v___x_3351_ = l_Lean_MessageData_ofFormat(v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2));
v___x_3356_ = l_Lean_MessageData_ofFormat(v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object* v_x_3357_, lean_object* v_x_3358_){
_start:
{
if (lean_obj_tag(v_x_3358_) == 0)
{
return v_x_3357_;
}
else
{
lean_object* v_head_3359_; lean_object* v_tail_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3382_; 
v_head_3359_ = lean_ctor_get(v_x_3358_, 0);
v_tail_3360_ = lean_ctor_get(v_x_3358_, 1);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_x_3358_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3362_ = v_x_3358_;
v_isShared_3363_ = v_isSharedCheck_3382_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_tail_3360_);
lean_inc(v_head_3359_);
lean_dec(v_x_3358_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3382_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_before_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3380_; 
v_before_3364_ = lean_ctor_get(v_head_3359_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_head_3359_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v_head_3359_, 1);
lean_dec(v_unused_3381_);
v___x_3366_ = v_head_3359_;
v_isShared_3367_ = v_isSharedCheck_3380_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_before_3364_);
lean_dec(v_head_3359_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3380_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 7);
lean_ctor_set(v___x_3366_, 1, v___x_3368_);
lean_ctor_set(v___x_3366_, 0, v_x_3357_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_x_3357_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 7);
lean_ctor_set(v___x_3362_, 1, v___x_3371_);
lean_ctor_set(v___x_3362_, 0, v___x_3370_);
v___x_3373_ = v___x_3362_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = l_Lean_MessageData_ofSyntax(v_before_3364_);
v___x_3375_ = l_Lean_indentD(v___x_3374_);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3373_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v_x_3357_ = v___x_3376_;
v_x_3358_ = v_tail_3360_;
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
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_3387_ = l_Lean_MessageData_ofFormat(v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_3388_, lean_object* v_macroStack_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3390_);
v___x_3393_ = l_Lean_Elab_pp_macroStack;
v___x_3394_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_3392_, v___x_3393_);
lean_dec_ref(v___x_3392_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
lean_dec(v_macroStack_3389_);
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v_msgData_3388_);
return v___x_3395_;
}
else
{
if (lean_obj_tag(v_macroStack_3389_) == 0)
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_msgData_3388_);
return v___x_3396_;
}
else
{
lean_object* v_head_3397_; lean_object* v_after_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3413_; 
v_head_3397_ = lean_ctor_get(v_macroStack_3389_, 0);
lean_inc(v_head_3397_);
v_after_3398_ = lean_ctor_get(v_head_3397_, 1);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_head_3397_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v_head_3397_, 0);
lean_dec(v_unused_3414_);
v___x_3400_ = v_head_3397_;
v_isShared_3401_ = v_isSharedCheck_3413_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_after_3398_);
lean_dec(v_head_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3413_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 7);
lean_ctor_set(v___x_3400_, 1, v___x_3402_);
lean_ctor_set(v___x_3400_, 0, v_msgData_3388_);
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_msgData_3388_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v_msgData_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3405_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l_Lean_MessageData_ofSyntax(v_after_3398_);
v___x_3408_ = l_Lean_indentD(v___x_3407_);
v_msgData_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3409_, 0, v___x_3406_);
lean_ctor_set(v_msgData_3409_, 1, v___x_3408_);
v___x_3410_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_3409_, v_macroStack_3389_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3415_, lean_object* v_macroStack_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3415_, v_macroStack_3416_, v___y_3417_);
lean_dec_ref(v___y_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_ref_3428_; lean_object* v_macroStack_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v_a_3432_; lean_object* v___x_3433_; lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3442_; 
v_ref_3428_ = lean_ctor_get(v___y_3425_, 2);
v_macroStack_3429_ = lean_ctor_get(v___y_3421_, 1);
v___x_3430_ = l_Lean_Elab_getBetterRef(v_ref_3428_, v_macroStack_3429_);
v___x_3431_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_3420_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
lean_inc(v_macroStack_3429_);
v___x_3433_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_3432_, v_macroStack_3429_, v___y_3425_);
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3430_);
lean_ctor_set(v___x_3438_, 1, v_a_3434_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set_tag(v___x_3436_, 1);
lean_ctor_set(v___x_3436_, 0, v___x_3438_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
return v_res_3451_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__0));
v___x_3454_ = l_Lean_stringToMessageData(v___x_3453_);
return v___x_3454_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1);
v___x_3456_ = l_Lean_MessageData_ofExpr(v___x_3455_);
return v___x_3456_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2);
v___x_3458_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v___x_3457_);
return v___x_3459_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3460_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_3461_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
lean_ctor_set(v___x_3462_, 1, v___x_3460_);
return v___x_3462_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__5));
v___x_3465_ = l_Lean_stringToMessageData(v___x_3464_);
return v___x_3465_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__7));
v___x_3468_ = l_Lean_stringToMessageData(v___x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(lean_object* v_stx_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v_ty_x3f_3477_; uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v_toCold_3483_; lean_object* v_currRecDepth_3484_; lean_object* v_ref_3485_; uint16_t v_optionFlags_3486_; uint8_t v_suppressElabErrors_3487_; uint8_t v_checkDeprecated_3488_; uint8_t v_isRecordingDeps_3489_; uint8_t v___x_3490_; lean_object* v_ref_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_ty_x3f_3477_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2);
v___x_3478_ = 1;
v___x_3479_ = lean_box(0);
v___x_3480_ = lean_box(v___x_3478_);
v___x_3481_ = lean_box(v___x_3478_);
lean_inc(v_stx_3469_);
v___x_3482_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3482_, 0, v_stx_3469_);
lean_closure_set(v___x_3482_, 1, v_ty_x3f_3477_);
lean_closure_set(v___x_3482_, 2, v___x_3480_);
lean_closure_set(v___x_3482_, 3, v___x_3481_);
lean_closure_set(v___x_3482_, 4, v___x_3479_);
v_toCold_3483_ = lean_ctor_get(v_a_3474_, 0);
v_currRecDepth_3484_ = lean_ctor_get(v_a_3474_, 1);
v_ref_3485_ = lean_ctor_get(v_a_3474_, 2);
v_optionFlags_3486_ = lean_ctor_get_uint16(v_a_3474_, sizeof(void*)*3);
v_suppressElabErrors_3487_ = lean_ctor_get_uint8(v_a_3474_, sizeof(void*)*3 + 2);
v_checkDeprecated_3488_ = lean_ctor_get_uint8(v_a_3474_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3489_ = lean_ctor_get_uint8(v_a_3474_, sizeof(void*)*3 + 4);
v___x_3490_ = 1;
v_ref_3491_ = l_Lean_replaceRef(v_stx_3469_, v_ref_3485_);
lean_dec(v_stx_3469_);
lean_inc(v_currRecDepth_3484_);
lean_inc_ref(v_toCold_3483_);
v___x_3492_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3492_, 0, v_toCold_3483_);
lean_ctor_set(v___x_3492_, 1, v_currRecDepth_3484_);
lean_ctor_set(v___x_3492_, 2, v_ref_3491_);
lean_ctor_set_uint16(v___x_3492_, sizeof(void*)*3, v_optionFlags_3486_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*3 + 2, v_suppressElabErrors_3487_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*3 + 3, v_checkDeprecated_3488_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*3 + 4, v_isRecordingDeps_3489_);
v___x_3493_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3482_, v___x_3490_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v___x_3492_, v_a_3475_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; lean_object* v_a_3496_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; uint8_t v___x_3580_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_3494_, v_a_3473_);
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref(v___x_3495_);
v___x_3580_ = l_Lean_Expr_hasSorry(v_a_3496_);
if (v___x_3580_ == 0)
{
v___y_3525_ = v_a_3470_;
v___y_3526_ = v_a_3471_;
v___y_3527_ = v_a_3472_;
v___y_3528_ = v_a_3473_;
v___y_3529_ = v___x_3492_;
v___y_3530_ = v_a_3475_;
goto v___jp_3524_;
}
else
{
uint8_t v___x_3581_; 
v___x_3581_ = l_Lean_Expr_hasSyntheticSorry(v_a_3496_);
if (v___x_3581_ == 0)
{
v___y_3562_ = v_a_3470_;
v___y_3563_ = v_a_3471_;
v___y_3564_ = v_a_3472_;
v___y_3565_ = v_a_3473_;
v___y_3566_ = v___x_3492_;
v___y_3567_ = v_a_3475_;
goto v___jp_3561_;
}
else
{
lean_object* v___x_3582_; lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v_a_3496_);
lean_dec_ref_known(v___x_3492_, 3);
v___x_3582_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
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
v___jp_3497_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3496_);
v___x_3505_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(v_a_3496_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_dec_ref(v___y_3502_);
lean_dec(v_a_3496_);
return v___x_3505_;
}
else
{
lean_object* v_a_3506_; uint8_t v___x_3507_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
v___x_3507_ = l_Lean_Exception_isInterrupt(v_a_3506_);
if (v___x_3507_ == 0)
{
uint8_t v___x_3508_; 
lean_inc(v_a_3506_);
v___x_3508_ = l_Lean_Exception_isRuntime(v_a_3506_);
if (v___x_3508_ == 0)
{
if (lean_obj_tag(v_a_3506_) == 0)
{
lean_dec_ref_known(v_a_3506_, 2);
lean_dec_ref(v___y_3502_);
lean_dec(v_a_3496_);
return v___x_3505_;
}
else
{
lean_object* v_id_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3522_; 
v_id_3509_ = lean_ctor_get(v_a_3506_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_a_3506_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; 
v_unused_3523_ = lean_ctor_get(v_a_3506_, 1);
lean_dec(v_unused_3523_);
v___x_3511_ = v_a_3506_;
v_isShared_3512_ = v_isSharedCheck_3522_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_id_3509_);
lean_dec(v_a_3506_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3522_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
uint8_t v___x_3513_; 
v___x_3513_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3504_, v_id_3509_);
lean_dec(v_id_3509_);
if (v___x_3513_ == 0)
{
lean_del_object(v___x_3511_);
lean_dec_ref(v___y_3502_);
lean_dec(v_a_3496_);
return v___x_3505_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec_ref_known(v___x_3505_, 1);
v___x_3514_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4);
v___x_3515_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6);
v___x_3516_ = l_Lean_indentExpr(v_a_3496_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set_tag(v___x_3511_, 7);
lean_ctor_set(v___x_3511_, 1, v___x_3516_);
lean_ctor_set(v___x_3511_, 0, v___x_3515_);
v___x_3518_ = v___x_3511_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___x_3514_);
v___x_3520_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3519_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec_ref(v___y_3502_);
return v___x_3520_;
}
}
}
}
}
else
{
lean_dec(v_a_3506_);
lean_dec_ref(v___y_3502_);
lean_dec(v_a_3496_);
return v___x_3505_;
}
}
else
{
lean_dec(v_a_3506_);
lean_dec_ref(v___y_3502_);
lean_dec(v_a_3496_);
return v___x_3505_;
}
}
}
v___jp_3524_:
{
lean_object* v___x_3531_; 
lean_inc(v_a_3496_);
v___x_3531_ = l_Lean_Meta_getMVars(v_a_3496_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3532_, v___x_3479_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v_a_3532_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; uint8_t v___x_3535_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = lean_unbox(v_a_3534_);
lean_dec(v_a_3534_);
if (v___x_3535_ == 0)
{
v___y_3498_ = v___y_3525_;
v___y_3499_ = v___y_3526_;
v___y_3500_ = v___y_3527_;
v___y_3501_ = v___y_3528_;
v___y_3502_ = v___y_3529_;
v___y_3503_ = v___y_3530_;
goto v___jp_3497_;
}
else
{
lean_object* v___x_3536_; lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v___y_3529_);
lean_dec(v_a_3496_);
v___x_3536_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v___y_3529_);
lean_dec(v_a_3496_);
v_a_3545_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3533_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3533_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v___y_3529_);
lean_dec(v_a_3496_);
v_a_3553_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3531_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3531_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
v___jp_3561_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v___x_3568_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8);
v___x_3569_ = l_Lean_indentExpr(v_a_3496_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3570_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec_ref(v___y_3566_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
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
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref_known(v___x_3492_, 3);
v_a_3591_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3493_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3493_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(v_stx_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(uint8_t v_config_3618_, lean_object* v_item_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_item_3628_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3632_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3619_, v___x_3631_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3632_) == 0)
{
uint8_t v___x_3633_; 
lean_dec_ref_known(v___x_3632_, 1);
v___x_3633_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3619_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3634_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3619_);
lean_inc_ref(v_item_3619_);
v___x_3635_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3619_);
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__1));
v___x_3637_ = lean_string_dec_eq(v___x_3634_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2));
v___x_3639_ = lean_string_dec_eq(v___x_3634_, v___x_3638_);
lean_dec_ref(v___x_3634_);
if (v___x_3639_ == 0)
{
lean_dec_ref(v_item_3619_);
v_item_3628_ = v___x_3635_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3));
v___x_3641_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3619_, v___x_3640_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3641_) == 0)
{
uint8_t v___x_3642_; 
lean_dec_ref_known(v___x_3641_, 1);
v___x_3642_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3635_);
if (v___x_3642_ == 0)
{
lean_dec_ref(v_item_3619_);
v_item_3628_ = v___x_3635_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3643_; 
lean_dec_ref(v___x_3635_);
v___x_3643_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_a_3652_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3643_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3643_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v___x_3635_);
lean_dec_ref(v_item_3619_);
v_a_3660_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3641_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3641_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
else
{
uint8_t v___x_3668_; 
lean_dec_ref(v___x_3634_);
v___x_3668_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3635_);
if (v___x_3668_ == 0)
{
lean_dec_ref(v_item_3619_);
v_item_3628_ = v___x_3635_;
goto v___jp_3627_;
}
else
{
lean_object* v_value_3669_; lean_object* v___x_3670_; 
lean_dec_ref(v___x_3635_);
v_value_3669_ = lean_ctor_get(v_item_3619_, 2);
lean_inc(v_value_3669_);
lean_dec_ref(v_item_3619_);
v___x_3670_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(v_value_3669_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
return v___x_3670_;
}
}
}
else
{
v_item_3628_ = v_item_3619_;
goto v___jp_3627_;
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec_ref(v_item_3619_);
v_a_3671_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3632_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3632_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
v___jp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__0));
v___x_3630_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3628_, v___x_3629_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
return v___x_3630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3679_, lean_object* v_item_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v_config_3601__boxed_3688_; lean_object* v_res_3689_; 
v_config_3601__boxed_3688_ = lean_unbox(v_config_3679_);
v_res_3689_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(v_config_3601__boxed_3688_, v_item_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3692_, v___y_3696_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(v_e_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_3728_, lean_object* v_msg_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3738_, lean_object* v_msg_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_3738_, v_msg_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_3748_, lean_object* v_macroStack_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3748_, v_macroStack_3749_, v___y_3754_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_3758_, lean_object* v_macroStack_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_3758_, v_macroStack_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3767_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_box(0);
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3770_ = l_Lean_mkConst(v___x_3769_, v___x_3768_);
return v___x_3770_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0);
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(uint8_t v_cfg_3773_, lean_object* v_cfgItem_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1);
v___x_3783_ = lean_box(v_cfg_3773_);
v___x_3784_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v___x_3783_, v_cfgItem_3774_, v___x_3782_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___boxed(lean_object* v_cfg_3785_, lean_object* v_cfgItem_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
uint8_t v_cfg_boxed_3794_; lean_object* v_res_3795_; 
v_cfg_boxed_3794_ = lean_unbox(v_cfg_3785_);
v_res_3795_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(v_cfg_boxed_3794_, v_cfgItem_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v_cfgItem_3786_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg(lean_object* v_cfg_3797_, uint8_t v_init_3798_, uint8_t v_logExceptions_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v_onErr_3804_; lean_object* v_eval_3805_; 
v_onErr_3804_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConstructorConfig___redArg___closed__0));
v_eval_3805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0));
if (v_logExceptions_3799_ == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = lean_box(v_init_3798_);
v___x_3807_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3805_, v___x_3806_, v_cfg_3797_, v_onErr_3804_, v_logExceptions_3799_, v_a_3801_, v_a_3802_);
return v___x_3807_;
}
else
{
uint8_t v_recover_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v_recover_3808_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*1);
v___x_3809_ = lean_box(v_init_3798_);
v___x_3810_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3805_, v___x_3809_, v_cfg_3797_, v_onErr_3804_, v_recover_3808_, v_a_3801_, v_a_3802_);
return v___x_3810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___boxed(lean_object* v_cfg_3811_, lean_object* v_init_3812_, lean_object* v_logExceptions_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
uint8_t v_init_boxed_3818_; uint8_t v_logExceptions_boxed_3819_; lean_object* v_res_3820_; 
v_init_boxed_3818_ = lean_unbox(v_init_3812_);
v_logExceptions_boxed_3819_ = lean_unbox(v_logExceptions_3813_);
v_res_3820_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v_cfg_3811_, v_init_boxed_3818_, v_logExceptions_boxed_3819_, v_a_3814_, v_a_3815_, v_a_3816_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig(lean_object* v_cfg_3821_, uint8_t v_init_3822_, uint8_t v_logExceptions_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v_cfg_3821_, v_init_3822_, v_logExceptions_3823_, v_a_3824_, v_a_3830_, v_a_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___boxed(lean_object* v_cfg_3834_, lean_object* v_init_3835_, lean_object* v_logExceptions_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
uint8_t v_init_boxed_3846_; uint8_t v_logExceptions_boxed_3847_; lean_object* v_res_3848_; 
v_init_boxed_3846_ = lean_unbox(v_init_3835_);
v_logExceptions_boxed_3847_ = lean_unbox(v_logExceptions_3836_);
v_res_3848_ = l_Lean_Elab_Tactic_elabConstructorConfig(v_cfg_3834_, v_init_boxed_3846_, v_logExceptions_boxed_3847_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(lean_object* v_a_3849_, lean_object* v_a_3850_){
_start:
{
if (lean_obj_tag(v_a_3849_) == 0)
{
lean_object* v___x_3851_; 
v___x_3851_ = l_List_reverse___redArg(v_a_3850_);
return v___x_3851_;
}
else
{
lean_object* v_head_3852_; lean_object* v_tail_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3866_; 
v_head_3852_ = lean_ctor_get(v_a_3849_, 0);
v_tail_3853_ = lean_ctor_get(v_a_3849_, 1);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_a_3849_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3855_ = v_a_3849_;
v_isShared_3856_ = v_isSharedCheck_3866_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_tail_3853_);
lean_inc(v_head_3852_);
lean_dec(v_a_3849_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3866_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3857_ = 0;
v___x_3858_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_3859_ = l_Lean_MessageData_ofConstName(v_head_3852_, v___x_3857_);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3858_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 1, v_a_3850_);
lean_ctor_set(v___x_3855_, 0, v___x_3861_);
v___x_3863_ = v___x_3855_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_a_3850_);
v___x_3863_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
v_a_3849_ = v_tail_3853_;
v_a_3850_ = v___x_3863_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3872_, lean_object* v_x_3873_){
_start:
{
if (lean_obj_tag(v_x_3873_) == 1)
{
lean_object* v_pre_3874_; 
v_pre_3874_ = lean_ctor_get(v_x_3873_, 0);
switch(lean_obj_tag(v_pre_3874_))
{
case 1:
{
lean_object* v_pre_3875_; 
v_pre_3875_ = lean_ctor_get(v_pre_3874_, 0);
switch(lean_obj_tag(v_pre_3875_))
{
case 0:
{
lean_object* v_str_3876_; lean_object* v_str_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v_str_3876_ = lean_ctor_get(v_x_3873_, 1);
v_str_3877_ = lean_ctor_get(v_pre_3874_, 1);
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1));
v___x_3879_ = lean_string_dec_eq(v_str_3877_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3880_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__2));
v___x_3881_ = lean_string_dec_eq(v_str_3877_, v___x_3880_);
if (v___x_3881_ == 0)
{
return v___x_3881_;
}
else
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__0));
v___x_3883_ = lean_string_dec_eq(v_str_3876_, v___x_3882_);
if (v___x_3883_ == 0)
{
return v___x_3883_;
}
else
{
return v_suppressElabErrors_3872_;
}
}
}
else
{
lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__1));
v___x_3885_ = lean_string_dec_eq(v_str_3876_, v___x_3884_);
if (v___x_3885_ == 0)
{
return v___x_3885_;
}
else
{
return v_suppressElabErrors_3872_;
}
}
}
case 1:
{
lean_object* v_pre_3886_; 
v_pre_3886_ = lean_ctor_get(v_pre_3875_, 0);
if (lean_obj_tag(v_pre_3886_) == 0)
{
lean_object* v_str_3887_; lean_object* v_str_3888_; lean_object* v_str_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v_str_3887_ = lean_ctor_get(v_x_3873_, 1);
v_str_3888_ = lean_ctor_get(v_pre_3874_, 1);
v_str_3889_ = lean_ctor_get(v_pre_3875_, 1);
v___x_3890_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__2));
v___x_3891_ = lean_string_dec_eq(v_str_3889_, v___x_3890_);
if (v___x_3891_ == 0)
{
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__3));
v___x_3893_ = lean_string_dec_eq(v_str_3888_, v___x_3892_);
if (v___x_3893_ == 0)
{
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__4));
v___x_3895_ = lean_string_dec_eq(v_str_3887_, v___x_3894_);
if (v___x_3895_ == 0)
{
return v___x_3895_;
}
else
{
return v_suppressElabErrors_3872_;
}
}
}
}
else
{
uint8_t v___x_3896_; 
v___x_3896_ = 0;
return v___x_3896_;
}
}
default: 
{
uint8_t v___x_3897_; 
v___x_3897_ = 0;
return v___x_3897_;
}
}
}
case 0:
{
lean_object* v_str_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_str_3898_ = lean_ctor_get(v_x_3873_, 1);
v___x_3899_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0));
v___x_3900_ = lean_string_dec_eq(v_str_3898_, v___x_3899_);
if (v___x_3900_ == 0)
{
return v___x_3900_;
}
else
{
return v_suppressElabErrors_3872_;
}
}
default: 
{
uint8_t v___x_3901_; 
v___x_3901_ = 0;
return v___x_3901_;
}
}
}
else
{
uint8_t v___x_3902_; 
v___x_3902_ = 0;
return v___x_3902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3903_, lean_object* v_x_3904_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3905_; uint8_t v_res_3906_; lean_object* v_r_3907_; 
v_suppressElabErrors_boxed_3905_ = lean_unbox(v_suppressElabErrors_3903_);
v_res_3906_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3905_, v_x_3904_);
lean_dec(v_x_3904_);
v_r_3907_ = lean_box(v_res_3906_);
return v_r_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_3909_, lean_object* v_msgData_3910_, uint8_t v_severity_3911_, uint8_t v_isSilent_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v___y_3919_; uint8_t v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; uint8_t v___y_3925_; lean_object* v_toCold_3926_; lean_object* v___y_3927_; lean_object* v___y_3956_; lean_object* v___y_3957_; uint8_t v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; uint8_t v___y_3961_; uint8_t v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3983_; uint8_t v___y_3984_; lean_object* v___y_3985_; uint8_t v___y_3986_; lean_object* v___y_3987_; uint8_t v___y_3988_; lean_object* v___y_3989_; uint8_t v___y_3993_; uint8_t v___y_3994_; uint8_t v___x_4004_; uint8_t v___y_4006_; uint8_t v___x_4012_; 
v___x_4004_ = 2;
v___x_4012_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3911_, v___x_4004_);
if (v___x_4012_ == 0)
{
v___y_4006_ = v___x_4012_;
goto v___jp_4005_;
}
else
{
uint8_t v___x_4013_; 
lean_inc_ref(v_msgData_3910_);
v___x_4013_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3910_);
if (v___x_4013_ == 0)
{
v___y_4006_ = v___x_4013_;
goto v___jp_4005_;
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec_ref(v_msgData_3910_);
v___x_4014_ = lean_box(0);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
return v___x_4015_;
}
}
v___jp_3918_:
{
lean_object* v_currNamespace_3928_; lean_object* v_openDecls_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v_env_3934_; lean_object* v_nextMacroScope_3935_; lean_object* v_ngen_3936_; lean_object* v_auxDeclNGen_3937_; lean_object* v_traceState_3938_; lean_object* v_cache_3939_; lean_object* v_recordedDeps_3940_; lean_object* v_messages_3941_; lean_object* v_infoState_3942_; lean_object* v_snapshotTasks_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3954_; 
v_currNamespace_3928_ = lean_ctor_get(v_toCold_3926_, 4);
v_openDecls_3929_ = lean_ctor_get(v_toCold_3926_, 5);
lean_inc(v_openDecls_3929_);
lean_inc(v_currNamespace_3928_);
v___x_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3930_, 0, v_currNamespace_3928_);
lean_ctor_set(v___x_3930_, 1, v_openDecls_3929_);
v___x_3931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v___y_3924_);
lean_inc_ref(v___y_3922_);
lean_inc_ref(v___y_3919_);
v___x_3932_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3932_, 0, v___y_3919_);
lean_ctor_set(v___x_3932_, 1, v___y_3923_);
lean_ctor_set(v___x_3932_, 2, v___y_3921_);
lean_ctor_set(v___x_3932_, 3, v___y_3922_);
lean_ctor_set(v___x_3932_, 4, v___x_3931_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*5, v___y_3925_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*5 + 1, v___y_3920_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*5 + 2, v_isSilent_3912_);
v___x_3933_ = lean_st_ref_take(v___y_3927_);
v_env_3934_ = lean_ctor_get(v___x_3933_, 0);
v_nextMacroScope_3935_ = lean_ctor_get(v___x_3933_, 1);
v_ngen_3936_ = lean_ctor_get(v___x_3933_, 2);
v_auxDeclNGen_3937_ = lean_ctor_get(v___x_3933_, 3);
v_traceState_3938_ = lean_ctor_get(v___x_3933_, 4);
v_cache_3939_ = lean_ctor_get(v___x_3933_, 5);
v_recordedDeps_3940_ = lean_ctor_get(v___x_3933_, 6);
v_messages_3941_ = lean_ctor_get(v___x_3933_, 7);
v_infoState_3942_ = lean_ctor_get(v___x_3933_, 8);
v_snapshotTasks_3943_ = lean_ctor_get(v___x_3933_, 9);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3945_ = v___x_3933_;
v_isShared_3946_ = v_isSharedCheck_3954_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_snapshotTasks_3943_);
lean_inc(v_infoState_3942_);
lean_inc(v_messages_3941_);
lean_inc(v_recordedDeps_3940_);
lean_inc(v_cache_3939_);
lean_inc(v_traceState_3938_);
lean_inc(v_auxDeclNGen_3937_);
lean_inc(v_ngen_3936_);
lean_inc(v_nextMacroScope_3935_);
lean_inc(v_env_3934_);
lean_dec(v___x_3933_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3954_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; 
v___x_3947_ = lean_box(0);
v___x_3948_ = l_Lean_MessageLog_add(v___x_3932_, v_messages_3941_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 7, v___x_3948_);
v___x_3950_ = v___x_3945_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_env_3934_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_nextMacroScope_3935_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_ngen_3936_);
lean_ctor_set(v_reuseFailAlloc_3953_, 3, v_auxDeclNGen_3937_);
lean_ctor_set(v_reuseFailAlloc_3953_, 4, v_traceState_3938_);
lean_ctor_set(v_reuseFailAlloc_3953_, 5, v_cache_3939_);
lean_ctor_set(v_reuseFailAlloc_3953_, 6, v_recordedDeps_3940_);
lean_ctor_set(v_reuseFailAlloc_3953_, 7, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3953_, 8, v_infoState_3942_);
lean_ctor_set(v_reuseFailAlloc_3953_, 9, v_snapshotTasks_3943_);
v___x_3950_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_st_ref_put(v___y_3927_, v___x_3950_);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3947_);
return v___x_3952_;
}
}
}
v___jp_3955_:
{
lean_object* v_fileName_3964_; lean_object* v_fileMap_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3981_; 
v_fileName_3964_ = lean_ctor_get(v___y_3959_, 0);
v_fileMap_3965_ = lean_ctor_get(v___y_3959_, 1);
v___x_3966_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3910_);
v___x_3967_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v___x_3966_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3970_ = v___x_3967_;
v_isShared_3971_ = v_isSharedCheck_3981_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3981_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_inc_ref_n(v_fileMap_3965_, 2);
v___x_3972_ = l_Lean_FileMap_toPosition(v_fileMap_3965_, v___y_3960_);
lean_dec(v___y_3960_);
v___x_3973_ = l_Lean_FileMap_toPosition(v_fileMap_3965_, v___y_3963_);
lean_dec(v___y_3963_);
v___x_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
v___x_3975_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___closed__0));
if (v___y_3961_ == 0)
{
lean_del_object(v___x_3970_);
lean_dec_ref(v___y_3957_);
v___y_3919_ = v_fileName_3964_;
v___y_3920_ = v___y_3958_;
v___y_3921_ = v___x_3974_;
v___y_3922_ = v___x_3975_;
v___y_3923_ = v___x_3972_;
v___y_3924_ = v_a_3968_;
v___y_3925_ = v___y_3962_;
v_toCold_3926_ = v___y_3956_;
v___y_3927_ = v___y_3916_;
goto v___jp_3918_;
}
else
{
uint8_t v___x_3976_; 
lean_inc(v_a_3968_);
v___x_3976_ = l_Lean_MessageData_hasTag(v___y_3957_, v_a_3968_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3979_; 
lean_dec_ref_known(v___x_3974_, 1);
lean_dec_ref(v___x_3972_);
lean_dec(v_a_3968_);
v___x_3977_ = lean_box(0);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3977_);
v___x_3979_ = v___x_3970_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
else
{
lean_del_object(v___x_3970_);
v___y_3919_ = v_fileName_3964_;
v___y_3920_ = v___y_3958_;
v___y_3921_ = v___x_3974_;
v___y_3922_ = v___x_3975_;
v___y_3923_ = v___x_3972_;
v___y_3924_ = v_a_3968_;
v___y_3925_ = v___y_3962_;
v_toCold_3926_ = v___y_3956_;
v___y_3927_ = v___y_3916_;
goto v___jp_3918_;
}
}
}
}
v___jp_3982_:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_Syntax_getTailPos_x3f(v___y_3987_, v___y_3988_);
lean_dec(v___y_3987_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_inc(v___y_3989_);
v___y_3956_ = v___y_3983_;
v___y_3957_ = v___y_3985_;
v___y_3958_ = v___y_3986_;
v___y_3959_ = v___y_3983_;
v___y_3960_ = v___y_3989_;
v___y_3961_ = v___y_3984_;
v___y_3962_ = v___y_3988_;
v___y_3963_ = v___y_3989_;
goto v___jp_3955_;
}
else
{
lean_object* v_val_3991_; 
v_val_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_val_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v___y_3956_ = v___y_3983_;
v___y_3957_ = v___y_3985_;
v___y_3958_ = v___y_3986_;
v___y_3959_ = v___y_3983_;
v___y_3960_ = v___y_3989_;
v___y_3961_ = v___y_3984_;
v___y_3962_ = v___y_3988_;
v___y_3963_ = v_val_3991_;
goto v___jp_3955_;
}
}
v___jp_3992_:
{
lean_object* v_toCold_3995_; lean_object* v_ref_3996_; uint8_t v_suppressElabErrors_3997_; lean_object* v___x_3998_; lean_object* v___f_3999_; lean_object* v_ref_4000_; lean_object* v___x_4001_; 
v_toCold_3995_ = lean_ctor_get(v___y_3915_, 0);
v_ref_3996_ = lean_ctor_get(v___y_3915_, 2);
v_suppressElabErrors_3997_ = lean_ctor_get_uint8(v___y_3915_, sizeof(void*)*3 + 2);
v___x_3998_ = lean_box(v_suppressElabErrors_3997_);
v___f_3999_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3999_, 0, v___x_3998_);
v_ref_4000_ = l_Lean_replaceRef(v_ref_3909_, v_ref_3996_);
v___x_4001_ = l_Lean_Syntax_getPos_x3f(v_ref_4000_, v___y_3993_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_unsigned_to_nat(0u);
v___y_3983_ = v_toCold_3995_;
v___y_3984_ = v_suppressElabErrors_3997_;
v___y_3985_ = v___f_3999_;
v___y_3986_ = v___y_3994_;
v___y_3987_ = v_ref_4000_;
v___y_3988_ = v___y_3993_;
v___y_3989_ = v___x_4002_;
goto v___jp_3982_;
}
else
{
lean_object* v_val_4003_; 
v_val_4003_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v___x_4001_, 1);
v___y_3983_ = v_toCold_3995_;
v___y_3984_ = v_suppressElabErrors_3997_;
v___y_3985_ = v___f_3999_;
v___y_3986_ = v___y_3994_;
v___y_3987_ = v_ref_4000_;
v___y_3988_ = v___y_3993_;
v___y_3989_ = v_val_4003_;
goto v___jp_3982_;
}
}
v___jp_4005_:
{
uint8_t v___x_4007_; uint8_t v___x_4008_; 
v___x_4007_ = 1;
v___x_4008_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3911_, v___x_4007_);
if (v___x_4008_ == 0)
{
v___y_3993_ = v___y_4006_;
v___y_3994_ = v_severity_3911_;
goto v___jp_3992_;
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4009_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3915_);
v___x_4010_ = l_Lean_warningAsError;
v___x_4011_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_4009_, v___x_4010_);
lean_dec_ref(v___x_4009_);
if (v___x_4011_ == 0)
{
v___y_3993_ = v___y_4006_;
v___y_3994_ = v_severity_3911_;
goto v___jp_3992_;
}
else
{
v___y_3993_ = v___y_4006_;
v___y_3994_ = v___x_4004_;
goto v___jp_3992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_4016_, lean_object* v_msgData_4017_, lean_object* v_severity_4018_, lean_object* v_isSilent_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
uint8_t v_severity_boxed_4025_; uint8_t v_isSilent_boxed_4026_; lean_object* v_res_4027_; 
v_severity_boxed_4025_ = lean_unbox(v_severity_4018_);
v_isSilent_boxed_4026_ = lean_unbox(v_isSilent_4019_);
v_res_4027_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4016_, v_msgData_4017_, v_severity_boxed_4025_, v_isSilent_boxed_4026_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v_ref_4016_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(lean_object* v_msgData_4028_, uint8_t v_severity_4029_, uint8_t v_isSilent_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_ref_4040_; lean_object* v___x_4041_; 
v_ref_4040_ = lean_ctor_get(v___y_4037_, 2);
v___x_4041_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4040_, v_msgData_4028_, v_severity_4029_, v_isSilent_4030_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1___boxed(lean_object* v_msgData_4042_, lean_object* v_severity_4043_, lean_object* v_isSilent_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
uint8_t v_severity_boxed_4054_; uint8_t v_isSilent_boxed_4055_; lean_object* v_res_4056_; 
v_severity_boxed_4054_ = lean_unbox(v_severity_4043_);
v_isSilent_boxed_4055_ = lean_unbox(v_isSilent_4044_);
v_res_4056_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(v_msgData_4042_, v_severity_boxed_4054_, v_isSilent_boxed_4055_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(lean_object* v_msgData_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
uint8_t v___x_4067_; uint8_t v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = 1;
v___x_4068_ = 0;
v___x_4069_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(v_msgData_4057_, v___x_4067_, v___x_4068_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1___boxed(lean_object* v_msgData_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(v_msgData_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4080_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__0));
v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__6));
v___x_4096_ = l_Lean_stringToMessageData(v___x_4095_);
return v___x_4096_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__8));
v___x_4099_ = l_Lean_stringToMessageData(v___x_4098_);
return v___x_4099_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__10));
v___x_4102_ = l_Lean_stringToMessageData(v___x_4101_);
return v___x_4102_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__12));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(lean_object* v_stx_4108_, lean_object* v___x_4109_, uint8_t v_cfg_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4112_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; uint8_t v___x_4122_; uint8_t v___x_4123_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___x_4146_; uint8_t v___y_4148_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v___x_4122_ = 1;
v___x_4123_ = 0;
v___x_4146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__2));
if (v_cfg_4110_ == 0)
{
v___y_4148_ = v___x_4122_;
goto v___jp_4147_;
}
else
{
v___y_4148_ = v___x_4123_;
goto v___jp_4147_;
}
v___jp_4124_:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4123_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v___x_4134_; 
lean_dec_ref_known(v___x_4133_, 1);
v___x_4134_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___y_4125_, v___y_4126_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4134_;
}
else
{
lean_dec(v___y_4125_);
return v___x_4133_;
}
}
v___jp_4135_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_inc_ref(v___y_4139_);
v___x_4140_ = l_Lean_stringToMessageData(v___y_4139_);
v___x_4141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___y_4138_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4141_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
lean_ctor_set(v___x_4144_, 1, v___y_4137_);
v___x_4145_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(v___x_4144_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_dec_ref_known(v___x_4145_, 1);
v___y_4125_ = v___y_4136_;
v___y_4126_ = v___y_4112_;
v___y_4127_ = v___y_4113_;
v___y_4128_ = v___y_4114_;
v___y_4129_ = v___y_4115_;
v___y_4130_ = v___y_4116_;
v___y_4131_ = v___y_4117_;
v___y_4132_ = v___y_4118_;
goto v___jp_4124_;
}
else
{
lean_dec(v___y_4136_);
return v___x_4145_;
}
}
v___jp_4147_:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_MVarId_constructorCore(v_a_4121_, v___x_4146_, v___y_4148_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v_fst_4151_; lean_object* v_snd_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4199_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v_fst_4151_ = lean_ctor_get(v_a_4150_, 0);
v_snd_4152_ = lean_ctor_get(v_a_4150_, 1);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_a_4150_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4154_ = v_a_4150_;
v_isShared_4155_ = v_isSharedCheck_4199_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_snd_4152_);
lean_inc(v_fst_4151_);
lean_dec(v_a_4150_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4199_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; 
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = lean_array_get_size(v_snd_4152_);
v___x_4158_ = lean_nat_dec_lt(v___x_4156_, v___x_4157_);
if (v___x_4158_ == 0)
{
lean_del_object(v___x_4154_);
lean_dec(v_snd_4152_);
v___y_4125_ = v_fst_4151_;
v___y_4126_ = v___y_4112_;
v___y_4127_ = v___y_4113_;
v___y_4128_ = v___y_4114_;
v___y_4129_ = v___y_4115_;
v___y_4130_ = v___y_4116_;
v___y_4131_ = v___y_4117_;
v___y_4132_ = v___y_4118_;
goto v___jp_4124_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_inc(v_snd_4152_);
v___x_4159_ = lean_array_to_list(v_snd_4152_);
v___x_4160_ = l_List_drop___redArg(v___x_4156_, v___x_4159_);
lean_dec(v___x_4159_);
v___x_4161_ = lean_box(0);
lean_inc(v___x_4160_);
v___x_4162_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(v___x_4160_, v___x_4161_);
v___x_4163_ = l_Lean_MessageData_andList(v___x_4162_);
v___x_4164_ = lean_box(0);
v___x_4165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__5));
v___x_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = l_Lean_Syntax_getArg(v_stx_4108_, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
v___x_4169_ = 4;
v___x_4170_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4170_, 0, v___x_4165_);
lean_ctor_set(v___x_4170_, 1, v___x_4168_);
lean_ctor_set(v___x_4170_, 2, v___x_4164_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*3, v___x_4169_);
v___x_4171_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7);
v___x_4172_ = lean_mk_empty_array_with_capacity(v___x_4156_);
v___x_4173_ = lean_array_push(v___x_4172_, v___x_4170_);
v___x_4174_ = l_Lean_MessageData_hint(v___x_4171_, v___x_4173_, v___x_4164_, v___x_4164_, v___x_4123_, v___y_4117_, v___y_4118_);
lean_dec_ref(v___x_4173_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4176_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9);
v___x_4177_ = lean_array_get(v___x_4109_, v_snd_4152_, v___x_4166_);
lean_dec(v_snd_4152_);
v___x_4178_ = l_Lean_MessageData_ofConstName(v___x_4177_, v___x_4123_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set_tag(v___x_4154_, 7);
lean_ctor_set(v___x_4154_, 1, v___x_4178_);
lean_ctor_set(v___x_4154_, 0, v___x_4176_);
v___x_4180_ = v___x_4154_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v___x_4181_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11);
v___x_4182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4180_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4163_);
v___x_4184_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13);
v___x_4185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4183_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = l_List_lengthTR___redArg(v___x_4160_);
lean_dec(v___x_4160_);
v___x_4187_ = lean_nat_dec_eq(v___x_4186_, v___x_4156_);
lean_dec(v___x_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; 
v___x_4188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__14));
v___y_4136_ = v_fst_4151_;
v___y_4137_ = v_a_4175_;
v___y_4138_ = v___x_4185_;
v___y_4139_ = v___x_4188_;
goto v___jp_4135_;
}
else
{
lean_object* v___x_4189_; 
v___x_4189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__15));
v___y_4136_ = v_fst_4151_;
v___y_4137_ = v_a_4175_;
v___y_4138_ = v___x_4185_;
v___y_4139_ = v___x_4189_;
goto v___jp_4135_;
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_dec_ref(v___x_4163_);
lean_dec(v___x_4160_);
lean_del_object(v___x_4154_);
lean_dec(v_snd_4152_);
lean_dec(v_fst_4151_);
v_a_4191_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4174_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4174_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
v_a_4200_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4149_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4149_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
v_a_4208_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4120_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4120_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed(lean_object* v_stx_4216_, lean_object* v___x_4217_, lean_object* v_cfg_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
uint8_t v_cfg_boxed_4228_; lean_object* v_res_4229_; 
v_cfg_boxed_4228_ = lean_unbox(v_cfg_4218_);
v_res_4229_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(v_stx_4216_, v___x_4217_, v_cfg_boxed_4228_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___x_4217_);
lean_dec(v_stx_4216_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(lean_object* v_stx_4230_, uint8_t v_cfg_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___f_4243_; lean_object* v___x_4244_; 
v___x_4241_ = lean_box(0);
v___x_4242_ = lean_box(v_cfg_4231_);
v___f_4243_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4243_, 0, v_stx_4230_);
lean_closure_set(v___f_4243_, 1, v___x_4241_);
lean_closure_set(v___f_4243_, 2, v___x_4242_);
v___x_4244_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4243_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___boxed(lean_object* v_stx_4245_, lean_object* v_cfg_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
uint8_t v_cfg_boxed_4256_; lean_object* v_res_4257_; 
v_cfg_boxed_4256_ = lean_unbox(v_cfg_4246_);
v_res_4257_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(v_stx_4245_, v_cfg_boxed_4256_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec_ref(v_a_4247_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(lean_object* v_ref_4258_, lean_object* v_msgData_4259_, uint8_t v_severity_4260_, uint8_t v_isSilent_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4258_, v_msgData_4259_, v_severity_4260_, v_isSilent_4261_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_4272_, lean_object* v_msgData_4273_, lean_object* v_severity_4274_, lean_object* v_isSilent_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
uint8_t v_severity_boxed_4285_; uint8_t v_isSilent_boxed_4286_; lean_object* v_res_4287_; 
v_severity_boxed_4285_ = lean_unbox(v_severity_4274_);
v_isSilent_boxed_4286_ = lean_unbox(v_isSilent_4275_);
v_res_4287_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(v_ref_4272_, v_msgData_4273_, v_severity_boxed_4285_, v_isSilent_boxed_4286_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v_ref_4272_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* v_stx_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; uint8_t v___x_4301_; lean_object* v___x_4302_; 
v___x_4298_ = lean_unsigned_to_nat(1u);
v___x_4299_ = l_Lean_Syntax_getArg(v_stx_4288_, v___x_4298_);
v___x_4300_ = 0;
v___x_4301_ = 1;
v___x_4302_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v___x_4299_, v___x_4300_, v___x_4301_, v_a_4289_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = lean_unbox(v_a_4303_);
lean_dec(v_a_4303_);
v___x_4305_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(v_stx_4288_, v___x_4304_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
return v___x_4305_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec(v_stx_4288_);
v_a_4306_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4302_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4302_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* v_stx_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_Elab_Tactic_evalConstructor(v_stx_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4338_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1));
v___x_4340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_4341_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 10, 0);
v___x_4342_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4338_, v___x_4339_, v___x_4340_, v___x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object* v_a_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_4372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6));
v___x_4373_ = l_Lean_addBuiltinDeclarationRanges(v___x_4371_, v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* v_stx_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v___y_4387_; lean_object* v___x_4396_; uint8_t v_transparency_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; uint8_t v___x_4401_; 
v___x_4396_ = l_Lean_Meta_Context_config(v_a_4381_);
v_transparency_4397_ = lean_ctor_get_uint8(v___x_4396_, 9);
lean_dec_ref(v___x_4396_);
v___x_4398_ = lean_unsigned_to_nat(1u);
v___x_4399_ = l_Lean_Syntax_getArg(v_stx_4376_, v___x_4398_);
v___x_4400_ = 2;
v___x_4401_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4397_, v___x_4400_);
if (v___x_4401_ == 0)
{
lean_object* v_keyedConfig_4402_; uint8_t v_trackZetaDelta_4403_; lean_object* v_zetaDeltaSet_4404_; lean_object* v_lctx_4405_; lean_object* v_localInstances_4406_; lean_object* v_defEqCtx_x3f_4407_; lean_object* v_synthPendingDepth_4408_; lean_object* v_customCanUnfoldPredicate_x3f_4409_; uint8_t v_univApprox_4410_; uint8_t v_inTypeClassResolution_4411_; uint8_t v_cacheInferType_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_keyedConfig_4402_ = lean_ctor_get(v_a_4381_, 0);
v_trackZetaDelta_4403_ = lean_ctor_get_uint8(v_a_4381_, sizeof(void*)*7);
v_zetaDeltaSet_4404_ = lean_ctor_get(v_a_4381_, 1);
v_lctx_4405_ = lean_ctor_get(v_a_4381_, 2);
v_localInstances_4406_ = lean_ctor_get(v_a_4381_, 3);
v_defEqCtx_x3f_4407_ = lean_ctor_get(v_a_4381_, 4);
v_synthPendingDepth_4408_ = lean_ctor_get(v_a_4381_, 5);
v_customCanUnfoldPredicate_x3f_4409_ = lean_ctor_get(v_a_4381_, 6);
v_univApprox_4410_ = lean_ctor_get_uint8(v_a_4381_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4411_ = lean_ctor_get_uint8(v_a_4381_, sizeof(void*)*7 + 2);
v_cacheInferType_4412_ = lean_ctor_get_uint8(v_a_4381_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4402_);
v___x_4413_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4400_, v_keyedConfig_4402_);
lean_inc(v_customCanUnfoldPredicate_x3f_4409_);
lean_inc(v_synthPendingDepth_4408_);
lean_inc(v_defEqCtx_x3f_4407_);
lean_inc_ref(v_localInstances_4406_);
lean_inc_ref(v_lctx_4405_);
lean_inc(v_zetaDeltaSet_4404_);
v___x_4414_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
lean_ctor_set(v___x_4414_, 1, v_zetaDeltaSet_4404_);
lean_ctor_set(v___x_4414_, 2, v_lctx_4405_);
lean_ctor_set(v___x_4414_, 3, v_localInstances_4406_);
lean_ctor_set(v___x_4414_, 4, v_defEqCtx_x3f_4407_);
lean_ctor_set(v___x_4414_, 5, v_synthPendingDepth_4408_);
lean_ctor_set(v___x_4414_, 6, v_customCanUnfoldPredicate_x3f_4409_);
lean_ctor_set_uint8(v___x_4414_, sizeof(void*)*7, v_trackZetaDelta_4403_);
lean_ctor_set_uint8(v___x_4414_, sizeof(void*)*7 + 1, v_univApprox_4410_);
lean_ctor_set_uint8(v___x_4414_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4411_);
lean_ctor_set_uint8(v___x_4414_, sizeof(void*)*7 + 3, v_cacheInferType_4412_);
v___x_4415_ = l_Lean_Elab_Tactic_evalTactic(v___x_4399_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v___x_4414_, v_a_4382_, v_a_4383_, v_a_4384_);
lean_dec_ref_known(v___x_4414_, 7);
v___y_4387_ = v___x_4415_;
goto v___jp_4386_;
}
else
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_Elab_Tactic_evalTactic(v___x_4399_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
v___y_4387_ = v___x_4416_;
goto v___jp_4386_;
}
v___jp_4386_:
{
if (lean_obj_tag(v___y_4387_) == 0)
{
return v___y_4387_;
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
v_a_4388_ = lean_ctor_get(v___y_4387_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___y_4387_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___y_4387_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___y_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object* v_stx_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_Elab_Tactic_evalWithReducible(v_stx_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
lean_dec(v_stx_4417_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4441_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1));
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_4444_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
v___x_4445_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4441_, v___x_4442_, v___x_4443_, v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6));
v___x_4476_ = l_Lean_addBuiltinDeclarationRanges(v___x_4474_, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* v_stx_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___y_4490_; lean_object* v___x_4499_; uint8_t v_transparency_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; uint8_t v___x_4503_; uint8_t v___x_4504_; 
v___x_4499_ = l_Lean_Meta_Context_config(v_a_4484_);
v_transparency_4500_ = lean_ctor_get_uint8(v___x_4499_, 9);
lean_dec_ref(v___x_4499_);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___x_4502_ = l_Lean_Syntax_getArg(v_stx_4479_, v___x_4501_);
v___x_4503_ = 3;
v___x_4504_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4500_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v_keyedConfig_4505_; uint8_t v_trackZetaDelta_4506_; lean_object* v_zetaDeltaSet_4507_; lean_object* v_lctx_4508_; lean_object* v_localInstances_4509_; lean_object* v_defEqCtx_x3f_4510_; lean_object* v_synthPendingDepth_4511_; lean_object* v_customCanUnfoldPredicate_x3f_4512_; uint8_t v_univApprox_4513_; uint8_t v_inTypeClassResolution_4514_; uint8_t v_cacheInferType_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_keyedConfig_4505_ = lean_ctor_get(v_a_4484_, 0);
v_trackZetaDelta_4506_ = lean_ctor_get_uint8(v_a_4484_, sizeof(void*)*7);
v_zetaDeltaSet_4507_ = lean_ctor_get(v_a_4484_, 1);
v_lctx_4508_ = lean_ctor_get(v_a_4484_, 2);
v_localInstances_4509_ = lean_ctor_get(v_a_4484_, 3);
v_defEqCtx_x3f_4510_ = lean_ctor_get(v_a_4484_, 4);
v_synthPendingDepth_4511_ = lean_ctor_get(v_a_4484_, 5);
v_customCanUnfoldPredicate_x3f_4512_ = lean_ctor_get(v_a_4484_, 6);
v_univApprox_4513_ = lean_ctor_get_uint8(v_a_4484_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4514_ = lean_ctor_get_uint8(v_a_4484_, sizeof(void*)*7 + 2);
v_cacheInferType_4515_ = lean_ctor_get_uint8(v_a_4484_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4505_);
v___x_4516_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4503_, v_keyedConfig_4505_);
lean_inc(v_customCanUnfoldPredicate_x3f_4512_);
lean_inc(v_synthPendingDepth_4511_);
lean_inc(v_defEqCtx_x3f_4510_);
lean_inc_ref(v_localInstances_4509_);
lean_inc_ref(v_lctx_4508_);
lean_inc(v_zetaDeltaSet_4507_);
v___x_4517_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
lean_ctor_set(v___x_4517_, 1, v_zetaDeltaSet_4507_);
lean_ctor_set(v___x_4517_, 2, v_lctx_4508_);
lean_ctor_set(v___x_4517_, 3, v_localInstances_4509_);
lean_ctor_set(v___x_4517_, 4, v_defEqCtx_x3f_4510_);
lean_ctor_set(v___x_4517_, 5, v_synthPendingDepth_4511_);
lean_ctor_set(v___x_4517_, 6, v_customCanUnfoldPredicate_x3f_4512_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*7, v_trackZetaDelta_4506_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*7 + 1, v_univApprox_4513_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4514_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*7 + 3, v_cacheInferType_4515_);
v___x_4518_ = l_Lean_Elab_Tactic_evalTactic(v___x_4502_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v___x_4517_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec_ref_known(v___x_4517_, 7);
v___y_4490_ = v___x_4518_;
goto v___jp_4489_;
}
else
{
lean_object* v___x_4519_; 
v___x_4519_ = l_Lean_Elab_Tactic_evalTactic(v___x_4502_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
v___y_4490_ = v___x_4519_;
goto v___jp_4489_;
}
v___jp_4489_:
{
if (lean_obj_tag(v___y_4490_) == 0)
{
return v___y_4490_;
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
v_a_4491_ = lean_ctor_get(v___y_4490_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___y_4490_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___y_4490_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___y_4490_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object* v_stx_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(v_stx_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_stx_4520_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4544_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1));
v___x_4546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_4547_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
v___x_4548_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4544_, v___x_4545_, v___x_4546_, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_4578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6));
v___x_4579_ = l_Lean_addBuiltinDeclarationRanges(v___x_4577_, v___x_4578_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit(lean_object* v_stx_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___y_4593_; lean_object* v___x_4602_; uint8_t v_transparency_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; uint8_t v___x_4607_; 
v___x_4602_ = l_Lean_Meta_Context_config(v_a_4587_);
v_transparency_4603_ = lean_ctor_get_uint8(v___x_4602_, 9);
lean_dec_ref(v___x_4602_);
v___x_4604_ = lean_unsigned_to_nat(1u);
v___x_4605_ = l_Lean_Syntax_getArg(v_stx_4582_, v___x_4604_);
v___x_4606_ = 5;
v___x_4607_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4603_, v___x_4606_);
if (v___x_4607_ == 0)
{
lean_object* v_keyedConfig_4608_; uint8_t v_trackZetaDelta_4609_; lean_object* v_zetaDeltaSet_4610_; lean_object* v_lctx_4611_; lean_object* v_localInstances_4612_; lean_object* v_defEqCtx_x3f_4613_; lean_object* v_synthPendingDepth_4614_; lean_object* v_customCanUnfoldPredicate_x3f_4615_; uint8_t v_univApprox_4616_; uint8_t v_inTypeClassResolution_4617_; uint8_t v_cacheInferType_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v_keyedConfig_4608_ = lean_ctor_get(v_a_4587_, 0);
v_trackZetaDelta_4609_ = lean_ctor_get_uint8(v_a_4587_, sizeof(void*)*7);
v_zetaDeltaSet_4610_ = lean_ctor_get(v_a_4587_, 1);
v_lctx_4611_ = lean_ctor_get(v_a_4587_, 2);
v_localInstances_4612_ = lean_ctor_get(v_a_4587_, 3);
v_defEqCtx_x3f_4613_ = lean_ctor_get(v_a_4587_, 4);
v_synthPendingDepth_4614_ = lean_ctor_get(v_a_4587_, 5);
v_customCanUnfoldPredicate_x3f_4615_ = lean_ctor_get(v_a_4587_, 6);
v_univApprox_4616_ = lean_ctor_get_uint8(v_a_4587_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4617_ = lean_ctor_get_uint8(v_a_4587_, sizeof(void*)*7 + 2);
v_cacheInferType_4618_ = lean_ctor_get_uint8(v_a_4587_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4608_);
v___x_4619_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4606_, v_keyedConfig_4608_);
lean_inc(v_customCanUnfoldPredicate_x3f_4615_);
lean_inc(v_synthPendingDepth_4614_);
lean_inc(v_defEqCtx_x3f_4613_);
lean_inc_ref(v_localInstances_4612_);
lean_inc_ref(v_lctx_4611_);
lean_inc(v_zetaDeltaSet_4610_);
v___x_4620_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
lean_ctor_set(v___x_4620_, 1, v_zetaDeltaSet_4610_);
lean_ctor_set(v___x_4620_, 2, v_lctx_4611_);
lean_ctor_set(v___x_4620_, 3, v_localInstances_4612_);
lean_ctor_set(v___x_4620_, 4, v_defEqCtx_x3f_4613_);
lean_ctor_set(v___x_4620_, 5, v_synthPendingDepth_4614_);
lean_ctor_set(v___x_4620_, 6, v_customCanUnfoldPredicate_x3f_4615_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*7, v_trackZetaDelta_4609_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*7 + 1, v_univApprox_4616_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4617_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*7 + 3, v_cacheInferType_4618_);
v___x_4621_ = l_Lean_Elab_Tactic_evalTactic(v___x_4605_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v___x_4620_, v_a_4588_, v_a_4589_, v_a_4590_);
lean_dec_ref_known(v___x_4620_, 7);
v___y_4593_ = v___x_4621_;
goto v___jp_4592_;
}
else
{
lean_object* v___x_4622_; 
v___x_4622_ = l_Lean_Elab_Tactic_evalTactic(v___x_4605_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
v___y_4593_ = v___x_4622_;
goto v___jp_4592_;
}
v___jp_4592_:
{
if (lean_obj_tag(v___y_4593_) == 0)
{
return v___y_4593_;
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
v_a_4594_ = lean_ctor_get(v___y_4593_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___y_4593_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___y_4593_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___y_4593_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit___boxed(lean_object* v_stx_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_Elab_Tactic_evalWithImplicit(v_stx_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_stx_4623_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1(){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4647_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1));
v___x_4649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3));
v___x_4650_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithImplicit___boxed), 10, 0);
v___x_4651_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4647_, v___x_4648_, v___x_4649_, v___x_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___boxed(lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* v_stx_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v___y_4665_; lean_object* v___x_4674_; uint8_t v_transparency_4675_; uint8_t v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v___x_4674_ = l_Lean_Meta_Context_config(v_a_4659_);
v_transparency_4675_ = lean_ctor_get_uint8(v___x_4674_, 9);
lean_dec_ref(v___x_4674_);
v___x_4676_ = 0;
v___x_4677_ = lean_unsigned_to_nat(1u);
v___x_4678_ = l_Lean_Syntax_getArg(v_stx_4654_, v___x_4677_);
v___x_4679_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4675_, v___x_4676_);
if (v___x_4679_ == 0)
{
lean_object* v_keyedConfig_4680_; uint8_t v_trackZetaDelta_4681_; lean_object* v_zetaDeltaSet_4682_; lean_object* v_lctx_4683_; lean_object* v_localInstances_4684_; lean_object* v_defEqCtx_x3f_4685_; lean_object* v_synthPendingDepth_4686_; lean_object* v_customCanUnfoldPredicate_x3f_4687_; uint8_t v_univApprox_4688_; uint8_t v_inTypeClassResolution_4689_; uint8_t v_cacheInferType_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v_keyedConfig_4680_ = lean_ctor_get(v_a_4659_, 0);
v_trackZetaDelta_4681_ = lean_ctor_get_uint8(v_a_4659_, sizeof(void*)*7);
v_zetaDeltaSet_4682_ = lean_ctor_get(v_a_4659_, 1);
v_lctx_4683_ = lean_ctor_get(v_a_4659_, 2);
v_localInstances_4684_ = lean_ctor_get(v_a_4659_, 3);
v_defEqCtx_x3f_4685_ = lean_ctor_get(v_a_4659_, 4);
v_synthPendingDepth_4686_ = lean_ctor_get(v_a_4659_, 5);
v_customCanUnfoldPredicate_x3f_4687_ = lean_ctor_get(v_a_4659_, 6);
v_univApprox_4688_ = lean_ctor_get_uint8(v_a_4659_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4689_ = lean_ctor_get_uint8(v_a_4659_, sizeof(void*)*7 + 2);
v_cacheInferType_4690_ = lean_ctor_get_uint8(v_a_4659_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4680_);
v___x_4691_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4676_, v_keyedConfig_4680_);
lean_inc(v_customCanUnfoldPredicate_x3f_4687_);
lean_inc(v_synthPendingDepth_4686_);
lean_inc(v_defEqCtx_x3f_4685_);
lean_inc_ref(v_localInstances_4684_);
lean_inc_ref(v_lctx_4683_);
lean_inc(v_zetaDeltaSet_4682_);
v___x_4692_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
lean_ctor_set(v___x_4692_, 1, v_zetaDeltaSet_4682_);
lean_ctor_set(v___x_4692_, 2, v_lctx_4683_);
lean_ctor_set(v___x_4692_, 3, v_localInstances_4684_);
lean_ctor_set(v___x_4692_, 4, v_defEqCtx_x3f_4685_);
lean_ctor_set(v___x_4692_, 5, v_synthPendingDepth_4686_);
lean_ctor_set(v___x_4692_, 6, v_customCanUnfoldPredicate_x3f_4687_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7, v_trackZetaDelta_4681_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 1, v_univApprox_4688_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4689_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 3, v_cacheInferType_4690_);
v___x_4693_ = l_Lean_Elab_Tactic_evalTactic(v___x_4678_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v___x_4692_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec_ref_known(v___x_4692_, 7);
v___y_4665_ = v___x_4693_;
goto v___jp_4664_;
}
else
{
lean_object* v___x_4694_; 
v___x_4694_ = l_Lean_Elab_Tactic_evalTactic(v___x_4678_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
v___y_4665_ = v___x_4694_;
goto v___jp_4664_;
}
v___jp_4664_:
{
if (lean_obj_tag(v___y_4665_) == 0)
{
return v___y_4665_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
v_a_4666_ = lean_ctor_get(v___y_4665_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___y_4665_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___y_4665_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___y_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object* v_stx_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Lean_Elab_Tactic_evalWithUnfoldingAll(v_stx_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
lean_dec(v_a_4703_);
lean_dec_ref(v_a_4702_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_stx_4695_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(){
_start:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4719_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1));
v___x_4721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_4722_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
v___x_4723_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4719_, v___x_4720_, v___x_4721_, v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_4753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6));
v___x_4754_ = l_Lean_addBuiltinDeclarationRanges(v___x_4752_, v___x_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object* v_a_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object* v_stx_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v___y_4768_; lean_object* v___x_4777_; uint8_t v_transparency_4778_; uint8_t v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4777_ = l_Lean_Meta_Context_config(v_a_4762_);
v_transparency_4778_ = lean_ctor_get_uint8(v___x_4777_, 9);
lean_dec_ref(v___x_4777_);
v___x_4779_ = 4;
v___x_4780_ = lean_unsigned_to_nat(1u);
v___x_4781_ = l_Lean_Syntax_getArg(v_stx_4757_, v___x_4780_);
v___x_4782_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4778_, v___x_4779_);
if (v___x_4782_ == 0)
{
lean_object* v_keyedConfig_4783_; uint8_t v_trackZetaDelta_4784_; lean_object* v_zetaDeltaSet_4785_; lean_object* v_lctx_4786_; lean_object* v_localInstances_4787_; lean_object* v_defEqCtx_x3f_4788_; lean_object* v_synthPendingDepth_4789_; lean_object* v_customCanUnfoldPredicate_x3f_4790_; uint8_t v_univApprox_4791_; uint8_t v_inTypeClassResolution_4792_; uint8_t v_cacheInferType_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v_keyedConfig_4783_ = lean_ctor_get(v_a_4762_, 0);
v_trackZetaDelta_4784_ = lean_ctor_get_uint8(v_a_4762_, sizeof(void*)*7);
v_zetaDeltaSet_4785_ = lean_ctor_get(v_a_4762_, 1);
v_lctx_4786_ = lean_ctor_get(v_a_4762_, 2);
v_localInstances_4787_ = lean_ctor_get(v_a_4762_, 3);
v_defEqCtx_x3f_4788_ = lean_ctor_get(v_a_4762_, 4);
v_synthPendingDepth_4789_ = lean_ctor_get(v_a_4762_, 5);
v_customCanUnfoldPredicate_x3f_4790_ = lean_ctor_get(v_a_4762_, 6);
v_univApprox_4791_ = lean_ctor_get_uint8(v_a_4762_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4792_ = lean_ctor_get_uint8(v_a_4762_, sizeof(void*)*7 + 2);
v_cacheInferType_4793_ = lean_ctor_get_uint8(v_a_4762_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4783_);
v___x_4794_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4779_, v_keyedConfig_4783_);
lean_inc(v_customCanUnfoldPredicate_x3f_4790_);
lean_inc(v_synthPendingDepth_4789_);
lean_inc(v_defEqCtx_x3f_4788_);
lean_inc_ref(v_localInstances_4787_);
lean_inc_ref(v_lctx_4786_);
lean_inc(v_zetaDeltaSet_4785_);
v___x_4795_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
lean_ctor_set(v___x_4795_, 1, v_zetaDeltaSet_4785_);
lean_ctor_set(v___x_4795_, 2, v_lctx_4786_);
lean_ctor_set(v___x_4795_, 3, v_localInstances_4787_);
lean_ctor_set(v___x_4795_, 4, v_defEqCtx_x3f_4788_);
lean_ctor_set(v___x_4795_, 5, v_synthPendingDepth_4789_);
lean_ctor_set(v___x_4795_, 6, v_customCanUnfoldPredicate_x3f_4790_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*7, v_trackZetaDelta_4784_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*7 + 1, v_univApprox_4791_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4792_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*7 + 3, v_cacheInferType_4793_);
v___x_4796_ = l_Lean_Elab_Tactic_evalTactic(v___x_4781_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v___x_4795_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec_ref_known(v___x_4795_, 7);
v___y_4768_ = v___x_4796_;
goto v___jp_4767_;
}
else
{
lean_object* v___x_4797_; 
v___x_4797_ = l_Lean_Elab_Tactic_evalTactic(v___x_4781_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
v___y_4768_ = v___x_4797_;
goto v___jp_4767_;
}
v___jp_4767_:
{
if (lean_obj_tag(v___y_4768_) == 0)
{
return v___y_4768_;
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
v_a_4769_ = lean_ctor_get(v___y_4768_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___y_4768_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___y_4768_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___y_4768_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object* v_stx_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Elab_Tactic_evalWithUnfoldingNone(v_stx_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_stx_4798_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1(){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4822_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1));
v___x_4824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3));
v___x_4825_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed), 10, 0);
v___x_4826_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4822_, v___x_4823_, v___x_4824_, v___x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object* v_stx_4832_, lean_object* v___x_4833_, uint8_t v___x_4834_, lean_object* v_userName_x3f_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l_Lean_Elab_Tactic_elabTerm(v_stx_4832_, v___x_4833_, v___x_4834_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4932_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4932_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4932_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
if (lean_obj_tag(v_a_4846_) == 1)
{
lean_object* v_fvarId_4850_; lean_object* v___x_4852_; 
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v_userName_x3f_4835_);
v_fvarId_4850_ = lean_ctor_get(v_a_4846_, 0);
lean_inc(v_fvarId_4850_);
lean_dec_ref_known(v_a_4846_, 1);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v_fvarId_4850_);
v___x_4852_ = v___x_4848_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_fvarId_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
else
{
lean_object* v___x_4854_; 
lean_del_object(v___x_4848_);
lean_inc(v___y_4843_);
lean_inc_ref(v___y_4842_);
lean_inc(v___y_4841_);
lean_inc_ref(v___y_4840_);
lean_inc(v_a_4846_);
v___x_4854_ = lean_infer_type(v_a_4846_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v_userName_4857_; uint8_t v_preserveBinderNames_4858_; lean_object* v___y_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v___y_4863_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
if (lean_obj_tag(v_userName_x3f_4835_) == 0)
{
lean_object* v___x_4921_; 
v___x_4921_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1));
v_userName_4857_ = v___x_4921_;
v_preserveBinderNames_4858_ = v___x_4834_;
v___y_4859_ = v___y_4837_;
v___y_4860_ = v___y_4840_;
v___y_4861_ = v___y_4841_;
v___y_4862_ = v___y_4842_;
v___y_4863_ = v___y_4843_;
goto v___jp_4856_;
}
else
{
lean_object* v_val_4922_; uint8_t v___x_4923_; 
v_val_4922_ = lean_ctor_get(v_userName_x3f_4835_, 0);
lean_inc(v_val_4922_);
lean_dec_ref_known(v_userName_x3f_4835_, 1);
v___x_4923_ = 1;
v_userName_4857_ = v_val_4922_;
v_preserveBinderNames_4858_ = v___x_4923_;
v___y_4859_ = v___y_4837_;
v___y_4860_ = v___y_4840_;
v___y_4861_ = v___y_4841_;
v___y_4862_ = v___y_4842_;
v___y_4863_ = v___y_4843_;
goto v___jp_4856_;
}
v___jp_4856_:
{
lean_object* v___x_4864_; 
v___x_4864_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = l_Lean_MVarId_assert(v_a_4865_, v_userName_4857_, v_a_4855_, v_a_4846_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v___x_4868_ = l_Lean_Meta_intro1Core(v_a_4867_, v_preserveBinderNames_4858_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v_fst_4870_; lean_object* v_snd_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4896_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref_known(v___x_4868_, 1);
v_fst_4870_ = lean_ctor_get(v_a_4869_, 0);
v_snd_4871_ = lean_ctor_get(v_a_4869_, 1);
v_isSharedCheck_4896_ = !lean_is_exclusive(v_a_4869_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4873_ = v_a_4869_;
v_isShared_4874_ = v_isSharedCheck_4896_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_snd_4871_);
lean_inc(v_fst_4870_);
lean_dec(v_a_4869_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4896_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4875_ = lean_box(0);
if (v_isShared_4874_ == 0)
{
lean_ctor_set_tag(v___x_4873_, 1);
lean_ctor_set(v___x_4873_, 1, v___x_4875_);
lean_ctor_set(v___x_4873_, 0, v_snd_4871_);
v___x_4877_ = v___x_4873_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_snd_4871_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4877_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; 
v_unused_4886_ = lean_ctor_get(v___x_4878_, 0);
lean_dec(v_unused_4886_);
v___x_4880_ = v___x_4878_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_dec(v___x_4878_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v_fst_4870_);
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_fst_4870_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v_fst_4870_);
v_a_4887_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4878_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4878_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
v_a_4897_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4868_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4868_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
v_a_4905_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4866_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4866_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v_userName_4857_);
lean_dec(v_a_4855_);
lean_dec(v_a_4846_);
v_a_4913_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4864_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4864_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
lean_dec(v_a_4846_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v_userName_x3f_4835_);
v_a_4924_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4854_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4854_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v_userName_x3f_4835_);
v_a_4933_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4845_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4845_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object* v_stx_4941_, lean_object* v___x_4942_, lean_object* v___x_4943_, lean_object* v_userName_x3f_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
uint8_t v___x_1502__boxed_4954_; lean_object* v_res_4955_; 
v___x_1502__boxed_4954_ = lean_unbox(v___x_4943_);
v_res_4955_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0(v_stx_4941_, v___x_4942_, v___x_1502__boxed_4954_, v_userName_x3f_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* v_stx_4956_, lean_object* v_userName_x3f_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v___x_4967_; uint8_t v___x_4968_; lean_object* v___x_4969_; lean_object* v___f_4970_; lean_object* v___x_4971_; 
v___x_4967_ = lean_box(0);
v___x_4968_ = 0;
v___x_4969_ = lean_box(v___x_4968_);
v___f_4970_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4970_, 0, v_stx_4956_);
lean_closure_set(v___f_4970_, 1, v___x_4967_);
lean_closure_set(v___f_4970_, 2, v___x_4969_);
lean_closure_set(v___f_4970_, 3, v_userName_x3f_4957_);
v___x_4971_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4970_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object* v_stx_4972_, lean_object* v_userName_x3f_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Elab_Tactic_elabAsFVar(v_stx_4972_, v_userName_x3f_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object* v_k_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; 
lean_inc(v___y_4988_);
lean_inc_ref(v___y_4987_);
lean_inc(v___y_4986_);
lean_inc_ref(v___y_4985_);
v___x_4994_ = lean_apply_9(v_k_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, lean_box(0));
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object* v_k_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(v_k_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object* v_k_5006_, uint8_t v_allowLevelAssignments_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v___f_5017_; lean_object* v___x_5018_; 
lean_inc(v___y_5011_);
lean_inc_ref(v___y_5010_);
lean_inc(v___y_5009_);
lean_inc_ref(v___y_5008_);
v___f_5017_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5017_, 0, v_k_5006_);
lean_closure_set(v___f_5017_, 1, v___y_5008_);
lean_closure_set(v___f_5017_, 2, v___y_5009_);
lean_closure_set(v___f_5017_, 3, v___y_5010_);
lean_closure_set(v___f_5017_, 4, v___y_5011_);
v___x_5018_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_5007_, v___f_5017_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
if (lean_obj_tag(v___x_5018_) == 0)
{
return v___x_5018_;
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object* v_k_5027_, lean_object* v_allowLevelAssignments_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5038_; lean_object* v_res_5039_; 
v_allowLevelAssignments_boxed_5038_ = lean_unbox(v_allowLevelAssignments_5028_);
v_res_5039_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_5027_, v_allowLevelAssignments_boxed_5038_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object* v_00_u03b1_5040_, lean_object* v_k_5041_, uint8_t v_allowLevelAssignments_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_5041_, v_allowLevelAssignments_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object* v_00_u03b1_5053_, lean_object* v_k_5054_, lean_object* v_allowLevelAssignments_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5065_; lean_object* v_res_5066_; 
v_allowLevelAssignments_boxed_5065_ = lean_unbox(v_allowLevelAssignments_5055_);
v_res_5066_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(v_00_u03b1_5053_, v_k_5054_, v_allowLevelAssignments_boxed_5065_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object* v_a_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v_a_x3f_5075_){
_start:
{
uint8_t v___x_5077_; lean_object* v___x_5078_; 
v___x_5077_ = 0;
v___x_5078_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_5067_, v___x_5077_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object* v_a_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v_a_x3f_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v_a_x3f_5087_);
lean_dec(v_a_x3f_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object* v_x_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v___x_5100_; 
v___x_5100_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_5092_, v___y_5094_, v___y_5096_, v___y_5098_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v_r_5102_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5101_);
lean_dec_ref_known(v___x_5100_, 1);
lean_inc(v___y_5098_);
lean_inc_ref(v___y_5097_);
lean_inc(v___y_5096_);
lean_inc_ref(v___y_5095_);
lean_inc(v___y_5094_);
lean_inc_ref(v___y_5093_);
lean_inc(v___y_5092_);
lean_inc_ref(v___y_5091_);
v_r_5102_ = lean_apply_9(v_x_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, lean_box(0));
if (lean_obj_tag(v_r_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5127_; 
v_a_5103_ = lean_ctor_get(v_r_5102_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_r_5102_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5105_ = v_r_5102_;
v_isShared_5106_ = v_isSharedCheck_5127_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v_r_5102_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5127_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
lean_inc(v_a_5103_);
if (v_isShared_5106_ == 0)
{
lean_ctor_set_tag(v___x_5105_, 1);
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5109_; 
v___x_5109_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5101_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___x_5108_);
lean_dec_ref(v___x_5108_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5116_ == 0)
{
lean_object* v_unused_5117_; 
v_unused_5117_ = lean_ctor_get(v___x_5109_, 0);
lean_dec(v_unused_5117_);
v___x_5111_ = v___x_5109_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_dec(v___x_5109_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
lean_ctor_set(v___x_5111_, 0, v_a_5103_);
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5103_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_dec(v_a_5103_);
v_a_5118_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5109_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5109_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v_a_5128_ = lean_ctor_get(v_r_5102_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v_r_5102_, 1);
v___x_5129_ = lean_box(0);
v___x_5130_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5101_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___x_5129_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5137_ == 0)
{
lean_object* v_unused_5138_; 
v_unused_5138_ = lean_ctor_get(v___x_5130_, 0);
lean_dec(v_unused_5138_);
v___x_5132_ = v___x_5130_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_dec(v___x_5130_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
lean_ctor_set_tag(v___x_5132_, 1);
lean_ctor_set(v___x_5132_, 0, v_a_5128_);
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5128_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
else
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_dec(v_a_5128_);
v_a_5139_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_5130_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5130_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec_ref(v_x_5090_);
v_a_5147_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5100_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5100_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object* v_x_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
lean_dec(v___y_5157_);
lean_dec_ref(v___y_5156_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object* v_00_u03b1_5166_, lean_object* v_x_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object* v_00_u03b1_5178_, lean_object* v_x_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(v_00_u03b1_5178_, v_x_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object* v_a_5190_, lean_object* v_as_5191_, lean_object* v_i_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v_zero_5198_; uint8_t v_isZero_5199_; 
v_zero_5198_ = lean_unsigned_to_nat(0u);
v_isZero_5199_ = lean_nat_dec_eq(v_i_5192_, v_zero_5198_);
if (v_isZero_5199_ == 1)
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
lean_dec(v_i_5192_);
lean_dec_ref(v_a_5190_);
v___x_5200_ = lean_box(0);
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
return v___x_5201_;
}
else
{
lean_object* v_one_5202_; lean_object* v_n_5203_; lean_object* v___x_5204_; 
v_one_5202_ = lean_unsigned_to_nat(1u);
v_n_5203_ = lean_nat_sub(v_i_5192_, v_one_5202_);
lean_dec(v_i_5192_);
v___x_5204_ = lean_array_fget(v_as_5191_, v_n_5203_);
if (lean_obj_tag(v___x_5204_) == 0)
{
v_i_5192_ = v_n_5203_;
goto _start;
}
else
{
lean_object* v_val_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5236_; 
v_val_5206_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5208_ = v___x_5204_;
v_isShared_5209_ = v_isSharedCheck_5236_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_val_5206_);
lean_dec(v___x_5204_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5236_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5210_ = l_Lean_LocalDecl_type(v_val_5206_);
lean_inc_ref(v_a_5190_);
v___x_5211_ = l_Lean_Meta_isExprDefEq(v_a_5190_, v___x_5210_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5227_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5214_ = v___x_5211_;
v_isShared_5215_ = v_isSharedCheck_5227_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5211_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5227_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
uint8_t v___x_5216_; 
v___x_5216_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5206_);
if (v___x_5216_ == 0)
{
uint8_t v___x_5217_; 
v___x_5217_ = lean_unbox(v_a_5212_);
lean_dec(v_a_5212_);
if (v___x_5217_ == 0)
{
lean_del_object(v___x_5214_);
lean_del_object(v___x_5208_);
lean_dec(v_val_5206_);
v_i_5192_ = v_n_5203_;
goto _start;
}
else
{
lean_object* v___x_5219_; lean_object* v___x_5221_; 
lean_dec(v_n_5203_);
lean_dec_ref(v_a_5190_);
v___x_5219_ = l_Lean_LocalDecl_fvarId(v_val_5206_);
lean_dec(v_val_5206_);
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 0, v___x_5219_);
v___x_5221_ = v___x_5208_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v___x_5219_);
v___x_5221_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
lean_object* v___x_5223_; 
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 0, v___x_5221_);
v___x_5223_ = v___x_5214_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5221_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
else
{
lean_del_object(v___x_5214_);
lean_dec(v_a_5212_);
lean_del_object(v___x_5208_);
lean_dec(v_val_5206_);
v_i_5192_ = v_n_5203_;
goto _start;
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_del_object(v___x_5208_);
lean_dec(v_val_5206_);
lean_dec(v_n_5203_);
lean_dec_ref(v_a_5190_);
v_a_5228_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5211_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5211_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_a_5237_, lean_object* v_as_5238_, lean_object* v_i_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5237_, v_as_5238_, v_i_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec_ref(v_as_5238_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_5246_, lean_object* v_as_5247_, lean_object* v_i_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_){
_start:
{
lean_object* v_zero_5258_; uint8_t v_isZero_5259_; 
v_zero_5258_ = lean_unsigned_to_nat(0u);
v_isZero_5259_ = lean_nat_dec_eq(v_i_5248_, v_zero_5258_);
if (v_isZero_5259_ == 1)
{
lean_object* v___x_5260_; lean_object* v___x_5261_; 
lean_dec(v_i_5248_);
lean_dec_ref(v_a_5246_);
v___x_5260_ = lean_box(0);
v___x_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
return v___x_5261_;
}
else
{
lean_object* v_one_5262_; lean_object* v_n_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v_one_5262_ = lean_unsigned_to_nat(1u);
v_n_5263_ = lean_nat_sub(v_i_5248_, v_one_5262_);
lean_dec(v_i_5248_);
v___x_5264_ = lean_array_fget_borrowed(v_as_5247_, v_n_5263_);
lean_inc_ref(v_a_5246_);
v___x_5265_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5246_, v___x_5264_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
if (lean_obj_tag(v___x_5265_) == 0)
{
lean_object* v_a_5266_; 
v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
if (lean_obj_tag(v_a_5266_) == 0)
{
lean_dec_ref_known(v___x_5265_, 1);
v_i_5248_ = v_n_5263_;
goto _start;
}
else
{
lean_dec(v_n_5263_);
lean_dec_ref(v_a_5246_);
return v___x_5265_;
}
}
else
{
lean_dec(v_n_5263_);
lean_dec_ref(v_a_5246_);
return v___x_5265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object* v_a_5268_, lean_object* v_x_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
if (lean_obj_tag(v_x_5269_) == 0)
{
lean_object* v_cs_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v_cs_5279_ = lean_ctor_get(v_x_5269_, 0);
v___x_5280_ = lean_array_get_size(v_cs_5279_);
v___x_5281_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5268_, v_cs_5279_, v___x_5280_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
return v___x_5281_;
}
else
{
lean_object* v_vs_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_vs_5282_ = lean_ctor_get(v_x_5269_, 0);
v___x_5283_ = lean_array_get_size(v_vs_5282_);
v___x_5284_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5268_, v_vs_5282_, v___x_5283_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
return v___x_5284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object* v_a_5285_, lean_object* v_x_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5285_, v_x_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec_ref(v_x_5286_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_5297_, lean_object* v_as_5298_, lean_object* v_i_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5297_, v_as_5298_, v_i_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec_ref(v_as_5298_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object* v_a_5310_, lean_object* v_t_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v_root_5321_; lean_object* v_tail_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v_root_5321_ = lean_ctor_get(v_t_5311_, 0);
v_tail_5322_ = lean_ctor_get(v_t_5311_, 1);
v___x_5323_ = lean_array_get_size(v_tail_5322_);
lean_inc_ref(v_a_5310_);
v___x_5324_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5310_, v_tail_5322_, v___x_5323_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
if (lean_obj_tag(v_a_5325_) == 0)
{
lean_object* v___x_5326_; 
lean_dec_ref_known(v___x_5324_, 1);
v___x_5326_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5310_, v_root_5321_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
return v___x_5326_;
}
else
{
lean_dec_ref(v_a_5310_);
return v___x_5324_;
}
}
else
{
lean_dec_ref(v_a_5310_);
return v___x_5324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object* v_a_5327_, lean_object* v_t_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_5327_, v_t_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec_ref(v_t_5328_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object* v_a_5339_, lean_object* v_lctx_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_){
_start:
{
lean_object* v_decls_5350_; lean_object* v___x_5351_; 
v_decls_5350_ = lean_ctor_get(v_lctx_5340_, 1);
v___x_5351_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_5339_, v_decls_5350_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
return v___x_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object* v_a_5352_, lean_object* v_lctx_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_5352_, v_lctx_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec_ref(v_lctx_5353_);
return v_res_5363_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0));
v___x_5366_ = l_Lean_stringToMessageData(v___x_5365_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object* v___x_5367_, lean_object* v___x_5368_, uint8_t v___x_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
lean_object* v___x_5379_; 
v___x_5379_ = l_Lean_Elab_Tactic_elabTerm(v___x_5367_, v___x_5368_, v___x_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v_lctx_5381_; lean_object* v___x_5382_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
lean_inc_n(v_a_5380_, 2);
lean_dec_ref_known(v___x_5379_, 1);
v_lctx_5381_ = lean_ctor_get(v___y_5374_, 2);
v___x_5382_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_5380_, v_lctx_5381_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
if (lean_obj_tag(v___x_5382_) == 0)
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5395_; 
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5382_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5385_ = v___x_5382_;
v_isShared_5386_ = v_isSharedCheck_5395_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5382_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5395_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
if (lean_obj_tag(v_a_5383_) == 0)
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_del_object(v___x_5385_);
v___x_5387_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRename___lam__0___closed__1, &l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1);
v___x_5388_ = l_Lean_indentExpr(v_a_5380_);
v___x_5389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5387_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
v___x_5390_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_5389_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
return v___x_5390_;
}
else
{
lean_object* v_val_5391_; lean_object* v___x_5393_; 
lean_dec(v_a_5380_);
v_val_5391_ = lean_ctor_get(v_a_5383_, 0);
lean_inc(v_val_5391_);
lean_dec_ref_known(v_a_5383_, 1);
if (v_isShared_5386_ == 0)
{
lean_ctor_set(v___x_5385_, 0, v_val_5391_);
v___x_5393_ = v___x_5385_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_val_5391_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_dec(v_a_5380_);
v_a_5396_ = lean_ctor_get(v___x_5382_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5382_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5382_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5382_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
v_a_5404_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5379_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5379_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object* v___x_5412_, lean_object* v___x_5413_, lean_object* v___x_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_){
_start:
{
uint8_t v___x_6712__boxed_5424_; lean_object* v_res_5425_; 
v___x_6712__boxed_5424_ = lean_unbox(v___x_5414_);
v_res_5425_ = l_Lean_Elab_Tactic_evalRename___lam__0(v___x_5412_, v___x_5413_, v___x_6712__boxed_5424_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
lean_dec(v___y_5422_);
lean_dec_ref(v___y_5421_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object* v___x_5426_, lean_object* v_h_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v___x_5437_; 
v___x_5437_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v___x_5426_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_object* v_a_5438_; lean_object* v___x_5439_; 
v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc(v_a_5438_);
lean_dec_ref_known(v___x_5437_, 1);
v___x_5439_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5429_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_a_5440_);
lean_dec_ref_known(v___x_5439_, 1);
v___x_5441_ = l_Lean_TSyntax_getId(v_h_5427_);
v___x_5442_ = l_Lean_MVarId_rename(v_a_5440_, v_a_5438_, v___x_5441_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v___x_5442_, 1);
v___x_5444_ = lean_box(0);
v___x_5445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5445_, 0, v_a_5443_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5445_, v___y_5429_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
return v___x_5446_;
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
v_a_5447_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5442_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5442_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_dec(v_a_5438_);
v_a_5455_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5439_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5439_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
v_a_5463_ = lean_ctor_get(v___x_5437_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5437_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5437_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5437_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object* v___x_5471_, lean_object* v_h_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_Elab_Tactic_evalRename___lam__1(v___x_5471_, v_h_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec(v___y_5478_);
lean_dec_ref(v___y_5477_);
lean_dec(v___y_5476_);
lean_dec_ref(v___y_5475_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec(v_h_5472_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* v_stx_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_){
_start:
{
lean_object* v___x_5502_; uint8_t v___x_5503_; 
v___x_5502_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
lean_inc(v_stx_5492_);
v___x_5503_ = l_Lean_Syntax_isOfKind(v_stx_5492_, v___x_5502_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; 
lean_dec(v_stx_5492_);
v___x_5504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_5504_;
}
else
{
lean_object* v___x_5505_; lean_object* v_h_5506_; lean_object* v___x_5507_; uint8_t v___x_5508_; 
v___x_5505_ = lean_unsigned_to_nat(3u);
v_h_5506_ = l_Lean_Syntax_getArg(v_stx_5492_, v___x_5505_);
v___x_5507_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__3));
lean_inc(v_h_5506_);
v___x_5508_ = l_Lean_Syntax_isOfKind(v_h_5506_, v___x_5507_);
if (v___x_5508_ == 0)
{
lean_object* v___x_5509_; 
lean_dec(v_h_5506_);
lean_dec(v_stx_5492_);
v___x_5509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_5509_;
}
else
{
lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___f_5514_; lean_object* v___x_5515_; uint8_t v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___f_5519_; lean_object* v___x_5520_; 
v___x_5510_ = lean_unsigned_to_nat(1u);
v___x_5511_ = l_Lean_Syntax_getArg(v_stx_5492_, v___x_5510_);
lean_dec(v_stx_5492_);
v___x_5512_ = lean_box(0);
v___x_5513_ = lean_box(v___x_5508_);
v___f_5514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__0___boxed), 12, 3);
lean_closure_set(v___f_5514_, 0, v___x_5511_);
lean_closure_set(v___f_5514_, 1, v___x_5512_);
lean_closure_set(v___f_5514_, 2, v___x_5513_);
v___x_5515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_5515_, 0, lean_box(0));
lean_closure_set(v___x_5515_, 1, v___f_5514_);
v___x_5516_ = 0;
v___x_5517_ = lean_box(v___x_5516_);
v___x_5518_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed), 12, 3);
lean_closure_set(v___x_5518_, 0, lean_box(0));
lean_closure_set(v___x_5518_, 1, v___x_5515_);
lean_closure_set(v___x_5518_, 2, v___x_5517_);
v___f_5519_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__1___boxed), 11, 2);
lean_closure_set(v___f_5519_, 0, v___x_5518_);
lean_closure_set(v___f_5519_, 1, v_h_5506_);
v___x_5520_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5519_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_);
return v___x_5520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object* v_stx_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l_Lean_Elab_Tactic_evalRename(v_stx_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
lean_dec(v_a_5527_);
lean_dec_ref(v_a_5526_);
lean_dec(v_a_5525_);
lean_dec_ref(v_a_5524_);
lean_dec(v_a_5523_);
lean_dec_ref(v_a_5522_);
return v_res_5531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object* v_a_5532_, lean_object* v_as_5533_, lean_object* v_i_5534_, lean_object* v_a_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_){
_start:
{
lean_object* v___x_5545_; 
v___x_5545_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5532_, v_as_5533_, v_i_5534_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_);
return v___x_5545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object* v_a_5546_, lean_object* v_as_5547_, lean_object* v_i_5548_, lean_object* v_a_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(v_a_5546_, v_as_5547_, v_i_5548_, v_a_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec_ref(v___y_5550_);
lean_dec_ref(v_as_5547_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object* v_a_5560_, lean_object* v_as_5561_, lean_object* v_i_5562_, lean_object* v_a_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_){
_start:
{
lean_object* v___x_5573_; 
v___x_5573_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5560_, v_as_5561_, v_i_5562_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_);
return v___x_5573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_a_5574_, lean_object* v_as_5575_, lean_object* v_i_5576_, lean_object* v_a_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_){
_start:
{
lean_object* v_res_5587_; 
v_res_5587_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(v_a_5574_, v_as_5575_, v_i_5576_, v_a_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
lean_dec(v___y_5585_);
lean_dec_ref(v___y_5584_);
lean_dec(v___y_5583_);
lean_dec_ref(v___y_5582_);
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec_ref(v_as_5575_);
return v_res_5587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(){
_start:
{
lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
v___x_5595_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5596_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
v___x_5597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_5598_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___boxed), 10, 0);
v___x_5599_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5595_, v___x_5596_, v___x_5597_, v___x_5598_);
return v___x_5599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object* v_a_5600_){
_start:
{
lean_object* v_res_5601_; 
v_res_5601_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
return v_res_5601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(){
_start:
{
lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_5629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6));
v___x_5630_ = l_Lean_addBuiltinDeclarationRanges(v___x_5628_, v___x_5629_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object* v_a_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
return v_res_5632_;
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
