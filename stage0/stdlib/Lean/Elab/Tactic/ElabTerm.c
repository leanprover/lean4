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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLetRecAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
lean_object* l_instMonadEIO(lean_object*);
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
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to find a hypothesis with type"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_options_149_; lean_object* v_declName_x3f_150_; lean_object* v_macroStack_151_; uint8_t v_mayPostpone_152_; uint8_t v_errToSorry_153_; lean_object* v_autoBoundImplicitContext_154_; lean_object* v_autoBoundImplicitForbidden_155_; lean_object* v_sectionVars_156_; lean_object* v_sectionFVars_157_; uint8_t v_implicitLambda_158_; uint8_t v_heedElabAsElim_159_; uint8_t v_isNoncomputableSection_160_; uint8_t v_isMetaSection_161_; uint8_t v_ignoreTCFailures_162_; uint8_t v_inPattern_163_; lean_object* v_tacSnap_x3f_164_; uint8_t v_saveRecAppSyntax_165_; uint8_t v_holesAsSyntheticOpaque_166_; uint8_t v_checkDeprecated_167_; lean_object* v_fixedTermElabs_168_; lean_object* v___y_170_; uint8_t v___y_174_; 
v_options_149_ = lean_ctor_get(v___y_146_, 1);
v_declName_x3f_150_ = lean_ctor_get(v___y_142_, 0);
v_macroStack_151_ = lean_ctor_get(v___y_142_, 1);
v_mayPostpone_152_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8);
v_errToSorry_153_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_154_ = lean_ctor_get(v___y_142_, 2);
v_autoBoundImplicitForbidden_155_ = lean_ctor_get(v___y_142_, 3);
v_sectionVars_156_ = lean_ctor_get(v___y_142_, 4);
v_sectionFVars_157_ = lean_ctor_get(v___y_142_, 5);
v_implicitLambda_158_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 2);
v_heedElabAsElim_159_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_160_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 4);
v_isMetaSection_161_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_162_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 6);
v_inPattern_163_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_164_ = lean_ctor_get(v___y_142_, 6);
v_saveRecAppSyntax_165_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_166_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 9);
v_checkDeprecated_167_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 10);
v_fixedTermElabs_168_ = lean_ctor_get(v___y_142_, 7);
if (lean_obj_tag(v_tacSnap_x3f_164_) == 0)
{
v___y_170_ = v_tacSnap_x3f_164_;
goto v___jp_169_;
}
else
{
lean_object* v_val_176_; lean_object* v_old_x3f_177_; lean_object* v___x_178_; lean_object* v___f_179_; 
v_val_176_ = lean_ctor_get(v_tacSnap_x3f_164_, 0);
v_old_x3f_177_ = lean_ctor_get(v_val_176_, 0);
v___x_178_ = lean_box(v_cond_138_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_179_, 0, v___x_178_);
if (lean_obj_tag(v_old_x3f_177_) == 1)
{
if (v_cond_138_ == 0)
{
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
else
{
lean_object* v_val_183_; lean_object* v_map_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_val_183_ = lean_ctor_get(v_old_x3f_177_, 0);
v_map_184_ = lean_ctor_get(v_options_149_, 0);
v___x_185_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3));
v___x_186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_184_, v___x_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_dec_ref(v___f_179_);
goto v___jp_180_;
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
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
else
{
lean_object* v_stx_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_stx_189_ = lean_ctor_get(v_val_183_, 0);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_190_, 0, v___f_179_);
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
v___y_174_ = v___x_200_;
goto v___jp_173_;
}
}
else
{
lean_dec(v_val_187_);
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
}
}
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
lean_dec_ref(v___f_179_);
v___x_201_ = lean_box(0);
v___x_202_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_201_);
v___y_174_ = v___x_202_;
goto v___jp_173_;
}
v___jp_180_:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_181_);
v___y_174_ = v___x_182_;
goto v___jp_173_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc_ref(v_fixedTermElabs_168_);
lean_inc(v_sectionFVars_157_);
lean_inc(v_sectionVars_156_);
lean_inc_ref(v_autoBoundImplicitForbidden_155_);
lean_inc(v_autoBoundImplicitContext_154_);
lean_inc(v_macroStack_151_);
lean_inc(v_declName_x3f_150_);
v___x_171_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_171_, 0, v_declName_x3f_150_);
lean_ctor_set(v___x_171_, 1, v_macroStack_151_);
lean_ctor_set(v___x_171_, 2, v_autoBoundImplicitContext_154_);
lean_ctor_set(v___x_171_, 3, v_autoBoundImplicitForbidden_155_);
lean_ctor_set(v___x_171_, 4, v_sectionVars_156_);
lean_ctor_set(v___x_171_, 5, v_sectionFVars_157_);
lean_ctor_set(v___x_171_, 6, v___y_170_);
lean_ctor_set(v___x_171_, 7, v_fixedTermElabs_168_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8, v_mayPostpone_152_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 1, v_errToSorry_153_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 2, v_implicitLambda_158_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 3, v_heedElabAsElim_159_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 4, v_isNoncomputableSection_160_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 5, v_isMetaSection_161_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 6, v_ignoreTCFailures_162_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 7, v_inPattern_163_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_165_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_166_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 10, v_checkDeprecated_167_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc(v___y_141_);
lean_inc_ref(v___y_140_);
v___x_172_ = lean_apply_9(v_act_139_, v___y_140_, v___y_141_, v___x_171_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
return v___x_172_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
v___y_170_ = v___x_175_;
goto v___jp_169_;
}
else
{
lean_inc(v_tacSnap_x3f_164_);
v___y_170_ = v_tacSnap_x3f_164_;
goto v___jp_169_;
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
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_toCold_421_; lean_object* v_options_422_; lean_object* v_currRecDepth_423_; lean_object* v_maxRecDepth_424_; lean_object* v_ref_425_; lean_object* v_currNamespace_426_; lean_object* v_openDecls_427_; lean_object* v_initHeartbeats_428_; lean_object* v_maxHeartbeats_429_; lean_object* v_currMacroScope_430_; uint8_t v_diag_431_; uint8_t v_suppressElabErrors_432_; lean_object* v_ref_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
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
v_options_422_ = lean_ctor_get(v_a_414_, 1);
v_currRecDepth_423_ = lean_ctor_get(v_a_414_, 2);
v_maxRecDepth_424_ = lean_ctor_get(v_a_414_, 3);
v_ref_425_ = lean_ctor_get(v_a_414_, 4);
v_currNamespace_426_ = lean_ctor_get(v_a_414_, 5);
v_openDecls_427_ = lean_ctor_get(v_a_414_, 6);
v_initHeartbeats_428_ = lean_ctor_get(v_a_414_, 7);
v_maxHeartbeats_429_ = lean_ctor_get(v_a_414_, 8);
v_currMacroScope_430_ = lean_ctor_get(v_a_414_, 9);
v_diag_431_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*10);
v_suppressElabErrors_432_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*10 + 1);
v_ref_433_ = l_Lean_replaceRef(v_stx_405_, v_ref_425_);
lean_dec(v_stx_405_);
lean_inc(v_currMacroScope_430_);
lean_inc(v_maxHeartbeats_429_);
lean_inc(v_initHeartbeats_428_);
lean_inc(v_openDecls_427_);
lean_inc(v_currNamespace_426_);
lean_inc(v_maxRecDepth_424_);
lean_inc(v_currRecDepth_423_);
lean_inc_ref(v_options_422_);
lean_inc_ref(v_toCold_421_);
v___x_434_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_434_, 0, v_toCold_421_);
lean_ctor_set(v___x_434_, 1, v_options_422_);
lean_ctor_set(v___x_434_, 2, v_currRecDepth_423_);
lean_ctor_set(v___x_434_, 3, v_maxRecDepth_424_);
lean_ctor_set(v___x_434_, 4, v_ref_433_);
lean_ctor_set(v___x_434_, 5, v_currNamespace_426_);
lean_ctor_set(v___x_434_, 6, v_openDecls_427_);
lean_ctor_set(v___x_434_, 7, v_initHeartbeats_428_);
lean_ctor_set(v___x_434_, 8, v_maxHeartbeats_429_);
lean_ctor_set(v___x_434_, 9, v_currMacroScope_430_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*10, v_diag_431_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*10 + 1, v_suppressElabErrors_432_);
v___x_435_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___x_420_, v_mayPostpone_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v___x_434_, v_a_415_);
lean_dec_ref_known(v___x_434_, 10);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_436_, v_a_413_);
return v___x_437_;
}
else
{
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object* v_stx_438_, lean_object* v_expectedType_x3f_439_, lean_object* v_mayPostpone_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
uint8_t v_mayPostpone_boxed_450_; lean_object* v_res_451_; 
v_mayPostpone_boxed_450_ = lean_unbox(v_mayPostpone_440_);
v_res_451_ = l_Lean_Elab_Tactic_elabTerm(v_stx_438_, v_expectedType_x3f_439_, v_mayPostpone_boxed_450_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object* v_stx_452_, lean_object* v_expectedType_x3f_453_, uint8_t v_mayPostpone_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
lean_inc(v_expectedType_x3f_453_);
v___x_464_ = l_Lean_Elab_Tactic_elabTerm(v_stx_452_, v_expectedType_x3f_453_, v_mayPostpone_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_464_) == 0)
{
if (lean_obj_tag(v_expectedType_x3f_453_) == 0)
{
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v_val_466_; lean_object* v___x_467_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_n(v_a_465_, 2);
lean_dec_ref_known(v___x_464_, 1);
v_val_466_ = lean_ctor_get(v_expectedType_x3f_453_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v_expectedType_x3f_453_, 1);
lean_inc(v_a_462_);
lean_inc_ref(v_a_461_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
v___x_467_ = lean_infer_type(v_a_465_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_549_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_549_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_549_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_549_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v_a_473_; lean_object* v___x_495_; uint8_t v_foApprox_496_; uint8_t v_ctxApprox_497_; uint8_t v_quasiPatternApprox_498_; uint8_t v_constApprox_499_; uint8_t v_isDefEqStuckEx_500_; uint8_t v_unificationHints_501_; uint8_t v_proofIrrelevance_502_; uint8_t v_offsetCnstrs_503_; uint8_t v_transparency_504_; uint8_t v_etaStruct_505_; uint8_t v_univApprox_506_; uint8_t v_iota_507_; uint8_t v_beta_508_; uint8_t v_proj_509_; uint8_t v_zeta_510_; uint8_t v_zetaDelta_511_; uint8_t v_zetaUnused_512_; uint8_t v_zetaHave_513_; uint8_t v_canUnfoldPredicateConfig_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_548_; 
v___x_495_ = l_Lean_Meta_Context_config(v_a_459_);
v_foApprox_496_ = lean_ctor_get_uint8(v___x_495_, 0);
v_ctxApprox_497_ = lean_ctor_get_uint8(v___x_495_, 1);
v_quasiPatternApprox_498_ = lean_ctor_get_uint8(v___x_495_, 2);
v_constApprox_499_ = lean_ctor_get_uint8(v___x_495_, 3);
v_isDefEqStuckEx_500_ = lean_ctor_get_uint8(v___x_495_, 4);
v_unificationHints_501_ = lean_ctor_get_uint8(v___x_495_, 5);
v_proofIrrelevance_502_ = lean_ctor_get_uint8(v___x_495_, 6);
v_offsetCnstrs_503_ = lean_ctor_get_uint8(v___x_495_, 8);
v_transparency_504_ = lean_ctor_get_uint8(v___x_495_, 9);
v_etaStruct_505_ = lean_ctor_get_uint8(v___x_495_, 10);
v_univApprox_506_ = lean_ctor_get_uint8(v___x_495_, 11);
v_iota_507_ = lean_ctor_get_uint8(v___x_495_, 12);
v_beta_508_ = lean_ctor_get_uint8(v___x_495_, 13);
v_proj_509_ = lean_ctor_get_uint8(v___x_495_, 14);
v_zeta_510_ = lean_ctor_get_uint8(v___x_495_, 15);
v_zetaDelta_511_ = lean_ctor_get_uint8(v___x_495_, 16);
v_zetaUnused_512_ = lean_ctor_get_uint8(v___x_495_, 17);
v_zetaHave_513_ = lean_ctor_get_uint8(v___x_495_, 18);
v_canUnfoldPredicateConfig_514_ = lean_ctor_get_uint8(v___x_495_, 19);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_548_ == 0)
{
v___x_516_ = v___x_495_;
v_isShared_517_ = v_isSharedCheck_548_;
goto v_resetjp_515_;
}
else
{
lean_dec(v___x_495_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_548_;
goto v_resetjp_515_;
}
v___jp_472_:
{
if (v_a_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_del_object(v___x_470_);
v___x_474_ = lean_box(0);
lean_inc(v_a_465_);
v___x_475_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_474_, v_val_466_, v_a_468_, v_a_465_, v___x_474_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_475_, 0);
lean_dec(v_unused_483_);
v___x_477_ = v___x_475_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_dec(v___x_475_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v_a_465_);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_465_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_a_465_);
v_a_484_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_475_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_475_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v___x_493_; 
lean_dec(v_a_468_);
lean_dec(v_val_466_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v_a_465_);
v___x_493_ = v___x_470_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_465_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
v_resetjp_515_:
{
uint8_t v_trackZetaDelta_518_; lean_object* v_zetaDeltaSet_519_; lean_object* v_lctx_520_; lean_object* v_localInstances_521_; lean_object* v_defEqCtx_x3f_522_; lean_object* v_synthPendingDepth_523_; lean_object* v_customCanUnfoldPredicate_x3f_524_; uint8_t v_univApprox_525_; uint8_t v_inTypeClassResolution_526_; uint8_t v_cacheInferType_527_; uint8_t v___x_528_; lean_object* v___x_530_; 
v_trackZetaDelta_518_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7);
v_zetaDeltaSet_519_ = lean_ctor_get(v_a_459_, 1);
v_lctx_520_ = lean_ctor_get(v_a_459_, 2);
v_localInstances_521_ = lean_ctor_get(v_a_459_, 3);
v_defEqCtx_x3f_522_ = lean_ctor_get(v_a_459_, 4);
v_synthPendingDepth_523_ = lean_ctor_get(v_a_459_, 5);
v_customCanUnfoldPredicate_x3f_524_ = lean_ctor_get(v_a_459_, 6);
v_univApprox_525_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_526_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7 + 2);
v_cacheInferType_527_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7 + 3);
v___x_528_ = 1;
if (v_isShared_517_ == 0)
{
v___x_530_ = v___x_516_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 0, v_foApprox_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 1, v_ctxApprox_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 2, v_quasiPatternApprox_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 3, v_constApprox_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 4, v_isDefEqStuckEx_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 5, v_unificationHints_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 6, v_proofIrrelevance_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 8, v_offsetCnstrs_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 9, v_transparency_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 10, v_etaStruct_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 11, v_univApprox_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 12, v_iota_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 13, v_beta_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 14, v_proj_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 15, v_zeta_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 16, v_zetaDelta_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 17, v_zetaUnused_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 18, v_zetaHave_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 19, v_canUnfoldPredicateConfig_514_);
v___x_530_ = v_reuseFailAlloc_547_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
uint64_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_ctor_set_uint8(v___x_530_, 7, v___x_528_);
v___x_531_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set_uint64(v___x_532_, sizeof(void*)*1, v___x_531_);
lean_inc(v_customCanUnfoldPredicate_x3f_524_);
lean_inc(v_synthPendingDepth_523_);
lean_inc(v_defEqCtx_x3f_522_);
lean_inc_ref(v_localInstances_521_);
lean_inc_ref(v_lctx_520_);
lean_inc(v_zetaDeltaSet_519_);
v___x_533_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_zetaDeltaSet_519_);
lean_ctor_set(v___x_533_, 2, v_lctx_520_);
lean_ctor_set(v___x_533_, 3, v_localInstances_521_);
lean_ctor_set(v___x_533_, 4, v_defEqCtx_x3f_522_);
lean_ctor_set(v___x_533_, 5, v_synthPendingDepth_523_);
lean_ctor_set(v___x_533_, 6, v_customCanUnfoldPredicate_x3f_524_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*7, v_trackZetaDelta_518_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*7 + 1, v_univApprox_525_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*7 + 2, v_inTypeClassResolution_526_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*7 + 3, v_cacheInferType_527_);
lean_inc(v_val_466_);
lean_inc(v_a_468_);
v___x_534_ = l_Lean_Meta_isExprDefEq(v_a_468_, v_val_466_, v___x_533_, v_a_460_, v_a_461_, v_a_462_);
lean_dec_ref_known(v___x_533_, 7);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; uint8_t v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = lean_unbox(v_a_535_);
lean_dec(v_a_535_);
v_a_473_ = v___x_536_;
goto v___jp_472_;
}
else
{
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_537_; uint8_t v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_534_, 1);
v___x_538_ = lean_unbox(v_a_537_);
lean_dec(v_a_537_);
v_a_473_ = v___x_538_;
goto v___jp_472_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_470_);
lean_dec(v_a_468_);
lean_dec(v_val_466_);
lean_dec(v_a_465_);
v_a_539_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_534_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_534_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
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
lean_dec(v_val_466_);
lean_dec(v_a_465_);
return v___x_467_;
}
}
}
else
{
lean_dec(v_expectedType_x3f_453_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* v_stx_550_, lean_object* v_expectedType_x3f_551_, lean_object* v_mayPostpone_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
uint8_t v_mayPostpone_boxed_562_; lean_object* v_res_563_; 
v_mayPostpone_boxed_562_ = lean_unbox(v_mayPostpone_552_);
v_res_563_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_stx_550_, v_expectedType_x3f_551_, v_mayPostpone_boxed_562_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_563_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_box(0);
v___x_565_ = l_Lean_Elab_abortTacticExceptionId;
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object* v_00_u03b1_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object* v_00_u03b1_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(v_00_u03b1_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object* v_mvarIds_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_box(0);
v___x_605_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_mvarIds_594_, v___x_604_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_616_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint8_t v___x_610_; 
v___x_610_ = lean_unbox(v_a_606_);
lean_dec(v_a_606_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
else
{
lean_object* v___x_615_; 
lean_del_object(v___x_608_);
v___x_615_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_615_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_605_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_605_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* v_mvarIds_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_mvarIds_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec_ref(v_mvarIds_625_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object* v___x_636_, lean_object* v_mvarCounterSaved_637_, lean_object* v_as_638_, size_t v_i_639_, size_t v_stop_640_, lean_object* v_b_641_){
_start:
{
lean_object* v___y_643_; uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_eq(v_i_639_, v_stop_640_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_index_650_; uint8_t v___x_651_; 
v___x_648_ = lean_array_uget_borrowed(v_as_638_, v_i_639_);
lean_inc(v___x_648_);
v___x_649_ = l_Lean_MetavarContext_getDecl(v___x_636_, v___x_648_);
v_index_650_ = lean_ctor_get(v___x_649_, 6);
lean_inc(v_index_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = lean_nat_dec_le(v_mvarCounterSaved_637_, v_index_650_);
lean_dec(v_index_650_);
if (v___x_651_ == 0)
{
v___y_643_ = v_b_641_;
goto v___jp_642_;
}
else
{
lean_object* v___x_652_; 
lean_inc(v___x_648_);
v___x_652_ = lean_array_push(v_b_641_, v___x_648_);
v___y_643_ = v___x_652_;
goto v___jp_642_;
}
}
else
{
return v_b_641_;
}
v___jp_642_:
{
size_t v___x_644_; size_t v___x_645_; 
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_639_, v___x_644_);
v_i_639_ = v___x_645_;
v_b_641_ = v___y_643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object* v___x_653_, lean_object* v_mvarCounterSaved_654_, lean_object* v_as_655_, lean_object* v_i_656_, lean_object* v_stop_657_, lean_object* v_b_658_){
_start:
{
size_t v_i_boxed_659_; size_t v_stop_boxed_660_; lean_object* v_res_661_; 
v_i_boxed_659_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_stop_boxed_660_ = lean_unbox_usize(v_stop_657_);
lean_dec(v_stop_657_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v___x_653_, v_mvarCounterSaved_654_, v_as_655_, v_i_boxed_659_, v_stop_boxed_660_, v_b_658_);
lean_dec_ref(v_as_655_);
lean_dec(v_mvarCounterSaved_654_);
lean_dec_ref(v___x_653_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object* v_mvarIds_664_, lean_object* v_mvarCounterSaved_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_668_ = lean_st_ref_get(v_a_666_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_array_get_size(v_mvarIds_664_);
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_672_ = lean_nat_dec_lt(v___x_669_, v___x_670_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v___x_668_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
return v___x_673_;
}
else
{
lean_object* v_mctx_674_; uint8_t v___x_675_; 
v_mctx_674_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_mctx_674_);
lean_dec(v___x_668_);
v___x_675_ = lean_nat_dec_le(v___x_670_, v___x_670_);
if (v___x_675_ == 0)
{
if (v___x_672_ == 0)
{
lean_object* v___x_676_; 
lean_dec_ref(v_mctx_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_671_);
return v___x_676_;
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_670_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_674_, v_mvarCounterSaved_665_, v_mvarIds_664_, v___x_677_, v___x_678_, v___x_671_);
lean_dec_ref(v_mctx_674_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
else
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_usize_of_nat(v___x_670_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_674_, v_mvarCounterSaved_665_, v_mvarIds_664_, v___x_681_, v___x_682_, v___x_671_);
lean_dec_ref(v_mctx_674_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object* v_mvarIds_685_, lean_object* v_mvarCounterSaved_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_685_, v_mvarCounterSaved_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec(v_mvarCounterSaved_686_);
lean_dec_ref(v_mvarIds_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* v_mvarIds_690_, lean_object* v_mvarCounterSaved_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_690_, v_mvarCounterSaved_691_, v_a_693_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* v_mvarIds_698_, lean_object* v_mvarCounterSaved_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Elab_Tactic_filterOldMVars(v_mvarIds_698_, v_mvarCounterSaved_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_mvarCounterSaved_699_);
lean_dec_ref(v_mvarIds_698_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
v___x_716_ = lean_apply_9(v_x_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object* v_x_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(v_x_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object* v_mvarId_728_, lean_object* v_x_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; 
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_739_, 0, v_x_729_);
lean_closure_set(v___f_739_, 1, v___y_730_);
lean_closure_set(v___f_739_, 2, v___y_731_);
lean_closure_set(v___f_739_, 3, v___y_732_);
lean_closure_set(v___f_739_, 4, v___y_733_);
v___x_740_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_728_, v___f_739_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_740_) == 0)
{
return v___x_740_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object* v_mvarId_749_, lean_object* v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_749_, v_x_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object* v_00_u03b1_761_, lean_object* v_mvarId_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_762_, v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object* v_00_u03b1_774_, lean_object* v_mvarId_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(v_00_u03b1_774_, v_mvarId_775_, v_x_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_786_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object* v_a_793_, lean_object* v_x_794_, lean_object* v_tacName_795_, uint8_t v_checkNewUnassigned_796_, lean_object* v_mvarCounter_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; 
lean_inc(v_a_793_);
v___x_807_ = l_Lean_MVarId_getType(v_a_793_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
lean_inc(v_a_793_);
v___x_809_ = l_Lean_MVarId_getTag(v_a_793_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
v___x_811_ = lean_apply_11(v_x_794_, v_a_808_, v_a_810_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, lean_box(0));
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
if (v_checkNewUnassigned_796_ == 0)
{
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
v___y_814_ = v___y_802_;
v___y_815_ = v___y_803_;
v___y_816_ = v___y_804_;
v___y_817_ = v___y_805_;
goto v___jp_813_;
}
else
{
lean_object* v___x_844_; 
lean_inc(v_a_812_);
v___x_844_ = l_Lean_Meta_getMVars(v_a_812_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_845_, v_mvarCounter_797_, v___y_803_);
lean_dec(v_a_845_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_847_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_a_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_dec_ref_known(v___x_848_, 1);
v___y_814_ = v___y_802_;
v___y_815_ = v___y_803_;
v___y_816_ = v___y_804_;
v___y_817_ = v___y_805_;
goto v___jp_813_;
}
else
{
lean_dec(v_a_812_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v_tacName_795_);
lean_dec(v_a_793_);
return v___x_848_;
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_a_812_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_tacName_795_);
lean_dec(v_a_793_);
v_a_849_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_844_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_844_);
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
v___jp_813_:
{
lean_object* v___x_818_; 
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v_a_812_);
lean_inc(v_a_793_);
v___x_818_ = lean_checked_assign(v_a_793_, v_a_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_835_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_835_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_835_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_835_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_821_);
v___x_824_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1);
v___x_825_ = l_Lean_indentExpr(v_a_812_);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = l_Lean_Meta_throwTacticEx___redArg(v_tacName_795_, v_a_793_, v___x_829_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v_a_812_);
lean_dec(v_tacName_795_);
lean_dec(v_a_793_);
v___x_831_ = lean_box(0);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_831_);
v___x_833_ = v___x_821_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
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
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v_a_812_);
lean_dec(v_tacName_795_);
lean_dec(v_a_793_);
v_a_836_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_818_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_818_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_tacName_795_);
lean_dec(v_a_793_);
v_a_857_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_811_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_811_);
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
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_a_808_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_tacName_795_);
lean_dec_ref(v_x_794_);
lean_dec(v_a_793_);
v_a_865_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_809_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_809_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_tacName_795_);
lean_dec_ref(v_x_794_);
lean_dec(v_a_793_);
v_a_873_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_807_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_807_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object* v_a_881_, lean_object* v_x_882_, lean_object* v_tacName_883_, lean_object* v_checkNewUnassigned_884_, lean_object* v_mvarCounter_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_895_; lean_object* v_res_896_; 
v_checkNewUnassigned_boxed_895_ = lean_unbox(v_checkNewUnassigned_884_);
v_res_896_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(v_a_881_, v_x_882_, v_tacName_883_, v_checkNewUnassigned_boxed_895_, v_mvarCounter_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v_mvarCounter_885_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* v_tacName_897_, lean_object* v_x_898_, uint8_t v_checkNewUnassigned_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_st_ref_get(v_a_905_);
v___x_910_ = l_Lean_Elab_Tactic_popMainGoal___redArg(v_a_901_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_mctx_911_; lean_object* v_a_912_; lean_object* v_mvarCounter_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; 
v_mctx_911_ = lean_ctor_get(v___x_909_, 0);
lean_inc_ref(v_mctx_911_);
lean_dec(v___x_909_);
v_a_912_ = lean_ctor_get(v___x_910_, 0);
lean_inc_n(v_a_912_, 3);
lean_dec_ref_known(v___x_910_, 1);
v_mvarCounter_913_ = lean_ctor_get(v_mctx_911_, 3);
lean_inc(v_mvarCounter_913_);
lean_dec_ref(v_mctx_911_);
v___x_914_ = lean_box(v_checkNewUnassigned_899_);
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed), 14, 5);
lean_closure_set(v___f_915_, 0, v_a_912_);
lean_closure_set(v___f_915_, 1, v_x_898_);
lean_closure_set(v___f_915_, 2, v_tacName_897_);
lean_closure_set(v___f_915_, 3, v___x_914_);
lean_closure_set(v___f_915_, 4, v_mvarCounter_913_);
v___x_916_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_a_912_, v___f_915_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_dec(v_a_912_);
return v___x_916_;
}
else
{
lean_object* v_a_917_; uint8_t v___y_919_; uint8_t v___x_929_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
v___x_929_ = l_Lean_Exception_isInterrupt(v_a_917_);
if (v___x_929_ == 0)
{
uint8_t v___x_930_; 
lean_inc(v_a_917_);
v___x_930_ = l_Lean_Exception_isRuntime(v_a_917_);
v___y_919_ = v___x_930_;
goto v___jp_918_;
}
else
{
v___y_919_ = v___x_929_;
goto v___jp_918_;
}
v___jp_918_:
{
if (v___y_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec_ref_known(v___x_916_, 1);
v___x_920_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_912_, v_a_901_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v___x_920_, 0);
lean_dec(v_unused_928_);
v___x_922_ = v___x_920_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_dec(v___x_920_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 0, v_a_917_);
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_917_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_dec(v_a_917_);
return v___x_920_;
}
}
else
{
lean_dec(v_a_917_);
lean_dec(v_a_912_);
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v___x_909_);
lean_dec_ref(v_x_898_);
lean_dec(v_tacName_897_);
v_a_931_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_910_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_910_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* v_tacName_939_, lean_object* v_x_940_, lean_object* v_checkNewUnassigned_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_951_; lean_object* v_res_952_; 
v_checkNewUnassigned_boxed_951_ = lean_unbox(v_checkNewUnassigned_941_);
v_res_952_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacName_939_, v_x_940_, v_checkNewUnassigned_boxed_951_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_952_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object* v_00_u03b1_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object* v_00_u03b1_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(v_00_u03b1_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object* v___x_983_, lean_object* v_type_984_, lean_object* v_x_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v_type_984_);
v___x_996_ = 0;
v___x_997_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_983_, v___x_995_, v___x_996_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object* v___x_998_, lean_object* v_type_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Elab_Tactic_evalExact___lam__0(v___x_998_, v_type_999_, v_x_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v_x_1000_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* v_stx_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
lean_inc(v_stx_1022_);
v___x_1033_ = l_Lean_Syntax_isOfKind(v_stx_1022_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec(v_stx_1022_);
v___x_1034_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = l_Lean_Syntax_getArg(v_stx_1022_, v___x_1035_);
lean_dec(v_stx_1022_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1037_, 0, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__5));
v___x_1039_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_1038_, v___f_1037_, v___x_1033_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object* v_stx_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Elab_Tactic_evalExact(v_stx_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
v___x_1060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1061_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___boxed), 10, 0);
v___x_1062_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1058_, v___x_1059_, v___x_1060_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6));
v___x_1093_ = l_Lean_addBuiltinDeclarationRanges(v___x_1091_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
return v_res_1095_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object* v_mctx_1096_, lean_object* v_mvarId_u2081_1097_, lean_object* v_mvarId_u2082_1098_){
_start:
{
lean_object* v_decl_u2081_1099_; lean_object* v_index_1100_; lean_object* v_decl_u2082_1101_; lean_object* v_index_1102_; uint8_t v___x_1103_; 
lean_inc(v_mvarId_u2081_1097_);
v_decl_u2081_1099_ = l_Lean_MetavarContext_getDecl(v_mctx_1096_, v_mvarId_u2081_1097_);
v_index_1100_ = lean_ctor_get(v_decl_u2081_1099_, 6);
lean_inc(v_index_1100_);
lean_dec_ref(v_decl_u2081_1099_);
lean_inc(v_mvarId_u2082_1098_);
v_decl_u2082_1101_ = l_Lean_MetavarContext_getDecl(v_mctx_1096_, v_mvarId_u2082_1098_);
v_index_1102_ = lean_ctor_get(v_decl_u2082_1101_, 6);
lean_inc(v_index_1102_);
lean_dec_ref(v_decl_u2082_1101_);
v___x_1103_ = lean_nat_dec_eq(v_index_1100_, v_index_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; 
lean_dec(v_mvarId_u2082_1098_);
lean_dec(v_mvarId_u2081_1097_);
v___x_1104_ = lean_nat_dec_lt(v_index_1100_, v_index_1102_);
lean_dec(v_index_1102_);
lean_dec(v_index_1100_);
return v___x_1104_;
}
else
{
uint8_t v___x_1105_; 
lean_dec(v_index_1102_);
lean_dec(v_index_1100_);
v___x_1105_ = l_Lean_Name_quickLt(v_mvarId_u2081_1097_, v_mvarId_u2082_1098_);
lean_dec(v_mvarId_u2082_1098_);
lean_dec(v_mvarId_u2081_1097_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object* v_mctx_1106_, lean_object* v_mvarId_u2081_1107_, lean_object* v_mvarId_u2082_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(v_mctx_1106_, v_mvarId_u2081_1107_, v_mvarId_u2082_1108_);
lean_dec_ref(v_mctx_1106_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object* v_mvarIds_1111_, lean_object* v_toPure_1112_, lean_object* v_mctx_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_array_get_size(v_mvarIds_1111_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_nat_dec_eq(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___f_1117_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___y_1126_; uint8_t v___x_1128_; 
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1117_, 0, v_mctx_1113_);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_nat_sub(v___x_1114_, v___x_1123_);
v___x_1128_ = lean_nat_dec_le(v___x_1115_, v___x_1124_);
if (v___x_1128_ == 0)
{
lean_inc(v___x_1124_);
v___y_1126_ = v___x_1124_;
goto v___jp_1125_;
}
else
{
v___y_1126_ = v___x_1115_;
goto v___jp_1125_;
}
v___jp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1117_, v___x_1114_, v_mvarIds_1111_, v___y_1119_, v___y_1120_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1120_);
v___x_1122_ = lean_apply_2(v_toPure_1112_, lean_box(0), v___x_1121_);
return v___x_1122_;
}
v___jp_1125_:
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_nat_dec_le(v___y_1126_, v___x_1124_);
if (v___x_1127_ == 0)
{
lean_dec(v___x_1124_);
lean_inc(v___y_1126_);
v___y_1119_ = v___y_1126_;
v___y_1120_ = v___y_1126_;
goto v___jp_1118_;
}
else
{
v___y_1119_ = v___y_1126_;
v___y_1120_ = v___x_1124_;
goto v___jp_1118_;
}
}
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v_mctx_1113_);
v___x_1129_ = lean_apply_2(v_toPure_1112_, lean_box(0), v_mvarIds_1111_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_mvarIds_1132_){
_start:
{
lean_object* v_toApplicative_1133_; lean_object* v_toBind_1134_; lean_object* v_getMCtx_1135_; lean_object* v_toPure_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; 
v_toApplicative_1133_ = lean_ctor_get(v_inst_1131_, 0);
lean_inc_ref(v_toApplicative_1133_);
v_toBind_1134_ = lean_ctor_get(v_inst_1131_, 1);
lean_inc(v_toBind_1134_);
lean_dec_ref(v_inst_1131_);
v_getMCtx_1135_ = lean_ctor_get(v_inst_1130_, 0);
lean_inc(v_getMCtx_1135_);
lean_dec_ref(v_inst_1130_);
v_toPure_1136_ = lean_ctor_get(v_toApplicative_1133_, 1);
lean_inc(v_toPure_1136_);
lean_dec_ref(v_toApplicative_1133_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1137_, 0, v_mvarIds_1132_);
lean_closure_set(v___f_1137_, 1, v_toPure_1136_);
v___x_1138_ = lean_apply_4(v_toBind_1134_, lean_box(0), lean_box(0), v_getMCtx_1135_, v___f_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_mvarIds_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1140_, v_inst_1141_, v_mvarIds_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_mvarIds_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1144_, v_inst_1145_, v_mvarIds_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* v_m_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_mvarIds_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1149_, v_inst_1150_, v_mvarIds_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v_mctx_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_st_ref_get(v___y_1154_);
v_mctx_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_mctx_1159_);
lean_dec(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_mctx_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object* v_val_1167_, lean_object* v_toPure_1168_, lean_object* v_newMVarIds_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_val_1167_);
lean_ctor_set(v___x_1170_, 1, v_newMVarIds_1169_);
v___x_1171_ = lean_apply_2(v_toPure_1168_, lean_box(0), v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_inst_1174_, lean_object* v_toBind_1175_, lean_object* v___f_1176_, lean_object* v_newMVarIds_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v___x_1172_, v___x_1173_, v_newMVarIds_1177_);
v___x_1179_ = lean_apply_2(v_inst_1174_, lean_box(0), v___x_1178_);
v___x_1180_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v___x_1179_, v___f_1176_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object* v_mvarCounter_1181_, lean_object* v_inst_1182_, lean_object* v_toBind_1183_, lean_object* v___f_1184_, lean_object* v_newMVarIds_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_filterOldMVars___boxed), 7, 2);
lean_closure_set(v___x_1186_, 0, v_newMVarIds_1185_);
lean_closure_set(v___x_1186_, 1, v_mvarCounter_1181_);
v___x_1187_ = lean_apply_2(v_inst_1182_, lean_box(0), v___x_1186_);
v___x_1188_ = lean_apply_4(v_toBind_1183_, lean_box(0), lean_box(0), v___x_1187_, v___f_1184_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object* v_toPure_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_inst_1192_, lean_object* v_toBind_1193_, lean_object* v_mvarCounter_1194_, lean_object* v_val_1195_){
_start:
{
lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_val_1195_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1196_, 0, v_val_1195_);
lean_closure_set(v___f_1196_, 1, v_toPure_1189_);
lean_inc_n(v_toBind_1193_, 2);
lean_inc_n(v_inst_1192_, 2);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1197_, 0, v___x_1190_);
lean_closure_set(v___f_1197_, 1, v___x_1191_);
lean_closure_set(v___f_1197_, 2, v_inst_1192_);
lean_closure_set(v___f_1197_, 3, v_toBind_1193_);
lean_closure_set(v___f_1197_, 4, v___f_1196_);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1198_, 0, v_mvarCounter_1194_);
lean_closure_set(v___f_1198_, 1, v_inst_1192_);
lean_closure_set(v___f_1198_, 2, v_toBind_1193_);
lean_closure_set(v___f_1198_, 3, v___f_1197_);
v___x_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_getMVarsNoDelayed___boxed), 6, 1);
lean_closure_set(v___x_1199_, 0, v_val_1195_);
v___x_1200_ = lean_apply_2(v_inst_1192_, lean_box(0), v___x_1199_);
v___x_1201_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v___x_1200_, v___f_1198_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object* v_toPure_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v_inst_1205_, lean_object* v_toBind_1206_, lean_object* v_k_1207_, lean_object* v_____do__lift_1208_){
_start:
{
lean_object* v_mvarCounter_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; 
v_mvarCounter_1209_ = lean_ctor_get(v_____do__lift_1208_, 3);
lean_inc(v_mvarCounter_1209_);
lean_dec_ref(v_____do__lift_1208_);
lean_inc(v_toBind_1206_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1210_, 0, v_toPure_1202_);
lean_closure_set(v___f_1210_, 1, v___x_1203_);
lean_closure_set(v___f_1210_, 2, v___x_1204_);
lean_closure_set(v___f_1210_, 3, v_inst_1205_);
lean_closure_set(v___f_1210_, 4, v_toBind_1206_);
lean_closure_set(v___f_1210_, 5, v_mvarCounter_1209_);
v___x_1211_ = lean_apply_4(v_toBind_1206_, lean_box(0), lean_box(0), v_k_1207_, v___f_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0(void){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_instMonadEIO(lean_box(0));
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0);
v___x_1214_ = l_StateRefT_x27_instMonad___redArg(v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_k_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_toApplicative_1225_; lean_object* v_toFunctor_1226_; lean_object* v_toSeq_1227_; lean_object* v_toSeqLeft_1228_; lean_object* v_toSeqRight_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_toApplicative_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1275_; 
v___x_1223_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_1224_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1);
v_toApplicative_1225_ = lean_ctor_get(v___x_1224_, 0);
v_toFunctor_1226_ = lean_ctor_get(v_toApplicative_1225_, 0);
v_toSeq_1227_ = lean_ctor_get(v_toApplicative_1225_, 2);
v_toSeqLeft_1228_ = lean_ctor_get(v_toApplicative_1225_, 3);
v_toSeqRight_1229_ = lean_ctor_get(v_toApplicative_1225_, 4);
v___f_1230_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2));
v___f_1231_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1226_, 2);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toFunctor_1226_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toFunctor_1226_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___f_1232_);
lean_ctor_set(v___x_1234_, 1, v___f_1233_);
lean_inc(v_toSeqRight_1229_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toSeqRight_1229_);
lean_inc(v_toSeqLeft_1228_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toSeqLeft_1228_);
lean_inc(v_toSeq_1227_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toSeq_1227_);
v___x_1238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1234_);
lean_ctor_set(v___x_1238_, 1, v___f_1230_);
lean_ctor_set(v___x_1238_, 2, v___f_1237_);
lean_ctor_set(v___x_1238_, 3, v___f_1236_);
lean_ctor_set(v___x_1238_, 4, v___f_1235_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___f_1231_);
v___x_1240_ = l_StateRefT_x27_instMonad___redArg(v___x_1239_);
v_toApplicative_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1240_, 1);
lean_dec(v_unused_1276_);
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1275_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_toApplicative_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1275_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_toFunctor_1245_; lean_object* v_toSeq_1246_; lean_object* v_toSeqLeft_1247_; lean_object* v_toSeqRight_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1273_; 
v_toFunctor_1245_ = lean_ctor_get(v_toApplicative_1241_, 0);
v_toSeq_1246_ = lean_ctor_get(v_toApplicative_1241_, 2);
v_toSeqLeft_1247_ = lean_ctor_get(v_toApplicative_1241_, 3);
v_toSeqRight_1248_ = lean_ctor_get(v_toApplicative_1241_, 4);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_toApplicative_1241_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_toApplicative_1241_, 1);
lean_dec(v_unused_1274_);
v___x_1250_ = v_toApplicative_1241_;
v_isShared_1251_ = v_isSharedCheck_1273_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_toSeqRight_1248_);
lean_inc(v_toSeqLeft_1247_);
lean_inc(v_toSeq_1246_);
lean_inc(v_toFunctor_1245_);
lean_dec(v_toApplicative_1241_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1273_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1261_; 
v___f_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4));
v___f_1253_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_1245_);
v___f_1254_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1254_, 0, v_toFunctor_1245_);
v___f_1255_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1255_, 0, v_toFunctor_1245_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___f_1254_);
lean_ctor_set(v___x_1256_, 1, v___f_1255_);
v___f_1257_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1257_, 0, v_toSeqRight_1248_);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toSeqLeft_1247_);
v___f_1259_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1259_, 0, v_toSeq_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 4, v___f_1257_);
lean_ctor_set(v___x_1250_, 3, v___f_1258_);
lean_ctor_set(v___x_1250_, 2, v___f_1259_);
lean_ctor_set(v___x_1250_, 1, v___f_1252_);
lean_ctor_set(v___x_1250_, 0, v___x_1256_);
v___x_1261_ = v___x_1250_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___f_1252_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v___f_1259_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___f_1258_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v___f_1257_);
v___x_1261_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___f_1253_);
lean_ctor_set(v___x_1243_, 0, v___x_1261_);
v___x_1263_ = v___x_1243_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___f_1253_);
v___x_1263_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v_toApplicative_1264_; lean_object* v_toBind_1265_; lean_object* v_toPure_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; 
v_toApplicative_1264_ = lean_ctor_get(v_inst_1220_, 0);
lean_inc_ref(v_toApplicative_1264_);
v_toBind_1265_ = lean_ctor_get(v_inst_1220_, 1);
lean_inc_n(v_toBind_1265_, 2);
lean_dec_ref(v_inst_1220_);
v_toPure_1266_ = lean_ctor_get(v_toApplicative_1264_, 1);
lean_inc(v_toPure_1266_);
lean_dec_ref(v_toApplicative_1264_);
v___f_1267_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6));
lean_inc(v_inst_1221_);
v___x_1268_ = lean_apply_2(v_inst_1221_, lean_box(0), v___f_1267_);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5), 7, 6);
lean_closure_set(v___f_1269_, 0, v_toPure_1266_);
lean_closure_set(v___f_1269_, 1, v___x_1223_);
lean_closure_set(v___f_1269_, 2, v___x_1263_);
lean_closure_set(v___f_1269_, 3, v_inst_1221_);
lean_closure_set(v___f_1269_, 4, v_toBind_1265_);
lean_closure_set(v___f_1269_, 5, v_k_1222_);
v___x_1270_ = lean_apply_4(v_toBind_1265_, lean_box(0), lean_box(0), v___x_1268_, v___f_1269_);
return v___x_1270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object* v_m_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg(v_inst_1278_, v_inst_1279_, v_k_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object* v_as_1282_, size_t v_i_1283_, size_t v_stop_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_a_1294_; uint8_t v___x_1298_; 
v___x_1298_ = lean_usize_dec_eq(v_i_1283_, v_stop_1284_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1302_; 
v___x_1299_ = lean_array_uget_borrowed(v_as_1282_, v_i_1283_);
lean_inc(v___x_1299_);
v___x_1302_ = l_Lean_Elab_Term_isLetRecAuxMVar(v___x_1299_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; uint8_t v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = lean_unbox(v_a_1303_);
lean_dec(v_a_1303_);
if (v___x_1304_ == 0)
{
goto v___jp_1300_;
}
else
{
v_a_1294_ = v_b_1285_;
goto v___jp_1293_;
}
}
else
{
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1305_; uint8_t v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1306_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
if (v___x_1306_ == 0)
{
v_a_1294_ = v_b_1285_;
goto v___jp_1293_;
}
else
{
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v_b_1285_);
v_a_1307_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1302_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1302_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1300_:
{
lean_object* v___x_1301_; 
lean_inc(v___x_1299_);
v___x_1301_ = lean_array_push(v_b_1285_, v___x_1299_);
v_a_1294_ = v___x_1301_;
goto v___jp_1293_;
}
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_b_1285_);
return v___x_1315_;
}
v___jp_1293_:
{
size_t v___x_1295_; size_t v___x_1296_; 
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1283_, v___x_1295_);
v_i_1283_ = v___x_1296_;
v_b_1285_ = v_a_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object* v_as_1316_, lean_object* v_i_1317_, lean_object* v_stop_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
size_t v_i_boxed_1327_; size_t v_stop_boxed_1328_; lean_object* v_res_1329_; 
v_i_boxed_1327_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_stop_boxed_1328_ = lean_unbox_usize(v_stop_1318_);
lean_dec(v_stop_1318_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1316_, v_i_boxed_1327_, v_stop_boxed_1328_, v_b_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_as_1316_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object* v_as_1330_, size_t v_i_1331_, size_t v_stop_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_usize_dec_eq(v_i_1331_, v_stop_1332_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_array_uget_borrowed(v_as_1330_, v_i_1331_);
lean_inc(v___x_1340_);
v___x_1341_ = l_Lean_MVarId_getKind(v___x_1340_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v_a_1344_; uint8_t v___x_1348_; uint8_t v___x_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1348_ = lean_unbox(v_a_1342_);
lean_dec(v_a_1342_);
v___x_1349_ = l_Lean_MetavarKind_isNatural(v___x_1348_);
if (v___x_1349_ == 0)
{
v_a_1344_ = v_b_1333_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1350_; 
lean_inc(v___x_1340_);
v___x_1350_ = lean_array_push(v_b_1333_, v___x_1340_);
v_a_1344_ = v___x_1350_;
goto v___jp_1343_;
}
v___jp_1343_:
{
size_t v___x_1345_; size_t v___x_1346_; 
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_add(v_i_1331_, v___x_1345_);
v_i_1331_ = v___x_1346_;
v_b_1333_ = v_a_1344_;
goto _start;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_b_1333_);
v_a_1351_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1341_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1341_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_b_1333_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object* v_as_1360_, lean_object* v_i_1361_, lean_object* v_stop_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
size_t v_i_boxed_1369_; size_t v_stop_boxed_1370_; lean_object* v_res_1371_; 
v_i_boxed_1369_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_stop_boxed_1370_ = lean_unbox_usize(v_stop_1362_);
lean_dec(v_stop_1362_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1360_, v_i_boxed_1369_, v_stop_boxed_1370_, v_b_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec_ref(v_as_1360_);
return v_res_1371_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___x_1372_, lean_object* v_mvarId_u2081_1373_, lean_object* v_mvarId_u2082_1374_){
_start:
{
lean_object* v_decl_u2081_1375_; lean_object* v_index_1376_; lean_object* v_decl_u2082_1377_; lean_object* v_index_1378_; uint8_t v___x_1379_; 
lean_inc(v_mvarId_u2081_1373_);
v_decl_u2081_1375_ = l_Lean_MetavarContext_getDecl(v___x_1372_, v_mvarId_u2081_1373_);
v_index_1376_ = lean_ctor_get(v_decl_u2081_1375_, 6);
lean_inc(v_index_1376_);
lean_dec_ref(v_decl_u2081_1375_);
lean_inc(v_mvarId_u2082_1374_);
v_decl_u2082_1377_ = l_Lean_MetavarContext_getDecl(v___x_1372_, v_mvarId_u2082_1374_);
v_index_1378_ = lean_ctor_get(v_decl_u2082_1377_, 6);
lean_inc(v_index_1378_);
lean_dec_ref(v_decl_u2082_1377_);
v___x_1379_ = lean_nat_dec_eq(v_index_1376_, v_index_1378_);
if (v___x_1379_ == 0)
{
uint8_t v___x_1380_; 
lean_dec(v_mvarId_u2082_1374_);
lean_dec(v_mvarId_u2081_1373_);
v___x_1380_ = lean_nat_dec_lt(v_index_1376_, v_index_1378_);
lean_dec(v_index_1378_);
lean_dec(v_index_1376_);
return v___x_1380_;
}
else
{
uint8_t v___x_1381_; 
lean_dec(v_index_1378_);
lean_dec(v_index_1376_);
v___x_1381_ = l_Lean_Name_quickLt(v_mvarId_u2081_1373_, v_mvarId_u2082_1374_);
lean_dec(v_mvarId_u2082_1374_);
lean_dec(v_mvarId_u2081_1373_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_1382_, lean_object* v_mvarId_u2081_1383_, lean_object* v_mvarId_u2082_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1382_, v_mvarId_u2081_1383_, v_mvarId_u2082_1384_);
lean_dec_ref(v___x_1382_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_1387_, lean_object* v_hi_1388_, lean_object* v_pivot_1389_, lean_object* v_as_1390_, lean_object* v_i_1391_, lean_object* v_k_1392_){
_start:
{
uint8_t v___y_1394_; uint8_t v___x_1403_; 
v___x_1403_ = lean_nat_dec_lt(v_k_1392_, v_hi_1388_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_k_1392_);
lean_dec(v_pivot_1389_);
v___x_1404_ = lean_array_fswap(v_as_1390_, v_i_1391_, v_hi_1388_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_i_1391_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v_decl_u2081_1407_; lean_object* v_index_1408_; lean_object* v_decl_u2082_1409_; lean_object* v_index_1410_; uint8_t v___x_1411_; 
v___x_1406_ = lean_array_fget_borrowed(v_as_1390_, v_k_1392_);
lean_inc(v___x_1406_);
v_decl_u2081_1407_ = l_Lean_MetavarContext_getDecl(v___x_1387_, v___x_1406_);
v_index_1408_ = lean_ctor_get(v_decl_u2081_1407_, 6);
lean_inc(v_index_1408_);
lean_dec_ref(v_decl_u2081_1407_);
lean_inc(v_pivot_1389_);
v_decl_u2082_1409_ = l_Lean_MetavarContext_getDecl(v___x_1387_, v_pivot_1389_);
v_index_1410_ = lean_ctor_get(v_decl_u2082_1409_, 6);
lean_inc(v_index_1410_);
lean_dec_ref(v_decl_u2082_1409_);
v___x_1411_ = lean_nat_dec_eq(v_index_1408_, v_index_1410_);
if (v___x_1411_ == 0)
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_lt(v_index_1408_, v_index_1410_);
lean_dec(v_index_1410_);
lean_dec(v_index_1408_);
v___y_1394_ = v___x_1412_;
goto v___jp_1393_;
}
else
{
uint8_t v___x_1413_; 
lean_dec(v_index_1410_);
lean_dec(v_index_1408_);
v___x_1413_ = l_Lean_Name_quickLt(v___x_1406_, v_pivot_1389_);
v___y_1394_ = v___x_1413_;
goto v___jp_1393_;
}
}
v___jp_1393_:
{
if (v___y_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_k_1392_, v___x_1395_);
lean_dec(v_k_1392_);
v_k_1392_ = v___x_1396_;
goto _start;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_array_fswap(v_as_1390_, v_i_1391_, v_k_1392_);
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_add(v_i_1391_, v___x_1399_);
lean_dec(v_i_1391_);
v___x_1401_ = lean_nat_add(v_k_1392_, v___x_1399_);
lean_dec(v_k_1392_);
v_as_1390_ = v___x_1398_;
v_i_1391_ = v___x_1400_;
v_k_1392_ = v___x_1401_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_1414_, lean_object* v_hi_1415_, lean_object* v_pivot_1416_, lean_object* v_as_1417_, lean_object* v_i_1418_, lean_object* v_k_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1414_, v_hi_1415_, v_pivot_1416_, v_as_1417_, v_i_1418_, v_k_1419_);
lean_dec(v_hi_1415_);
lean_dec_ref(v___x_1414_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object* v___x_1421_, lean_object* v_n_1422_, lean_object* v_as_1423_, lean_object* v_lo_1424_, lean_object* v_hi_1425_){
_start:
{
lean_object* v___y_1427_; uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_lt(v_lo_1424_, v_hi_1425_);
if (v___x_1437_ == 0)
{
lean_dec(v_lo_1424_);
return v_as_1423_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_mid_1440_; lean_object* v___y_1442_; lean_object* v___y_1448_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1438_ = lean_nat_add(v_lo_1424_, v_hi_1425_);
v___x_1439_ = lean_unsigned_to_nat(1u);
v_mid_1440_ = lean_nat_shiftr(v___x_1438_, v___x_1439_);
lean_dec(v___x_1438_);
v___x_1453_ = lean_array_fget_borrowed(v_as_1423_, v_mid_1440_);
v___x_1454_ = lean_array_fget_borrowed(v_as_1423_, v_lo_1424_);
lean_inc(v___x_1454_);
lean_inc(v___x_1453_);
v___x_1455_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1421_, v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
v___y_1448_ = v_as_1423_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_array_fswap(v_as_1423_, v_lo_1424_, v_mid_1440_);
v___y_1448_ = v___x_1456_;
goto v___jp_1447_;
}
v___jp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_array_fget_borrowed(v___y_1442_, v_mid_1440_);
v___x_1444_ = lean_array_fget_borrowed(v___y_1442_, v_hi_1425_);
lean_inc(v___x_1444_);
lean_inc(v___x_1443_);
v___x_1445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1421_, v___x_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v_mid_1440_);
v___y_1427_ = v___y_1442_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_array_fswap(v___y_1442_, v_mid_1440_, v_hi_1425_);
lean_dec(v_mid_1440_);
v___y_1427_ = v___x_1446_;
goto v___jp_1426_;
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_array_fget_borrowed(v___y_1448_, v_hi_1425_);
v___x_1450_ = lean_array_fget_borrowed(v___y_1448_, v_lo_1424_);
lean_inc(v___x_1450_);
lean_inc(v___x_1449_);
v___x_1451_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1421_, v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
v___y_1442_ = v___y_1448_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_array_fswap(v___y_1448_, v_lo_1424_, v_hi_1425_);
v___y_1442_ = v___x_1452_;
goto v___jp_1441_;
}
}
}
v___jp_1426_:
{
lean_object* v_pivot_1428_; lean_object* v___x_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; uint8_t v___x_1432_; 
v_pivot_1428_ = lean_array_fget(v___y_1427_, v_hi_1425_);
lean_inc_n(v_lo_1424_, 2);
v___x_1429_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1421_, v_hi_1425_, v_pivot_1428_, v___y_1427_, v_lo_1424_, v_lo_1424_);
v_fst_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_fst_1430_);
v_snd_1431_ = lean_ctor_get(v___x_1429_, 1);
lean_inc(v_snd_1431_);
lean_dec_ref(v___x_1429_);
v___x_1432_ = lean_nat_dec_le(v_hi_1425_, v_fst_1430_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1421_, v_n_1422_, v_snd_1431_, v_lo_1424_, v_fst_1430_);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_fst_1430_, v___x_1434_);
lean_dec(v_fst_1430_);
v_as_1423_ = v___x_1433_;
v_lo_1424_ = v___x_1435_;
goto _start;
}
else
{
lean_dec(v_fst_1430_);
lean_dec(v_lo_1424_);
return v_snd_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_1457_, lean_object* v_n_1458_, lean_object* v_as_1459_, lean_object* v_lo_1460_, lean_object* v_hi_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1457_, v_n_1458_, v_as_1459_, v_lo_1460_, v_hi_1461_);
lean_dec(v_hi_1461_);
lean_dec(v_n_1458_);
lean_dec_ref(v___x_1457_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object* v_mvarIds_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v_mctx_1467_; lean_object* v___x_1468_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1466_ = lean_st_ref_get(v___y_1464_);
v_mctx_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_mctx_1467_);
lean_dec(v___x_1466_);
v___x_1468_ = lean_array_get_size(v_mvarIds_1463_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_nat_dec_eq(v___x_1468_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___y_1479_; uint8_t v___x_1481_; 
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = lean_nat_sub(v___x_1468_, v___x_1476_);
v___x_1481_ = lean_nat_dec_le(v___x_1474_, v___x_1477_);
if (v___x_1481_ == 0)
{
lean_inc(v___x_1477_);
v___y_1479_ = v___x_1477_;
goto v___jp_1478_;
}
else
{
v___y_1479_ = v___x_1474_;
goto v___jp_1478_;
}
v___jp_1478_:
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_nat_dec_le(v___y_1479_, v___x_1477_);
if (v___x_1480_ == 0)
{
lean_dec(v___x_1477_);
lean_inc(v___y_1479_);
v___y_1470_ = v___y_1479_;
v___y_1471_ = v___y_1479_;
goto v___jp_1469_;
}
else
{
v___y_1470_ = v___y_1479_;
v___y_1471_ = v___x_1477_;
goto v___jp_1469_;
}
}
}
else
{
lean_object* v___x_1482_; 
lean_dec_ref(v_mctx_1467_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_mvarIds_1463_);
return v___x_1482_;
}
v___jp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v_mctx_1467_, v___x_1468_, v_mvarIds_1463_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v_mctx_1467_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object* v_mvarIds_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1483_, v___y_1484_);
lean_dec(v___y_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object* v_k_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v_mctx_1498_; lean_object* v_mvarCounter_1499_; lean_object* v___x_1500_; 
v___x_1497_ = lean_st_ref_get(v___y_1493_);
v_mctx_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_mctx_1498_);
lean_dec(v___x_1497_);
v_mvarCounter_1499_ = lean_ctor_get(v_mctx_1498_, 3);
lean_inc(v_mvarCounter_1499_);
lean_dec_ref(v_mctx_1498_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
v___x_1500_ = lean_apply_9(v_k_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, lean_box(0));
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_n(v_a_1501_, 2);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = l_Lean_Meta_getMVarsNoDelayed(v_a_1501_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v_a_1505_; lean_object* v___x_1506_; lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1515_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1504_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1503_, v_mvarCounter_1499_, v___y_1493_);
lean_dec(v_mvarCounter_1499_);
lean_dec(v_a_1503_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_a_1505_, v___y_1493_);
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_a_1501_);
lean_ctor_set(v___x_1511_, 1, v_a_1507_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1513_ = v___x_1509_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v_a_1501_);
lean_dec(v_mvarCounter_1499_);
v_a_1516_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1502_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1502_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_mvarCounter_1499_);
v_a_1524_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1500_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1500_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object* v_k_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* v_k_1543_, lean_object* v_parentTag_1544_, lean_object* v_tagSuffix_1545_, uint8_t v_allowNaturalHoles_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1543_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_fst_1558_; lean_object* v_snd_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1652_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v_fst_1558_ = lean_ctor_get(v_a_1557_, 0);
v_snd_1559_ = lean_ctor_get(v_a_1557_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1561_ = v_a_1557_;
v_isShared_1562_ = v_isSharedCheck_1652_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snd_1559_);
lean_inc(v_fst_1558_);
lean_dec(v_a_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1652_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1595_; lean_object* v_a_1596_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___x_1618_; lean_object* v_a_1620_; lean_object* v___y_1632_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_array_get_size(v_snd_1559_);
v___x_1643_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1644_ = lean_nat_dec_lt(v___x_1618_, v___x_1642_);
if (v___x_1644_ == 0)
{
lean_dec(v_snd_1559_);
v_a_1620_ = v___x_1643_;
goto v___jp_1619_;
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_le(v___x_1642_, v___x_1642_);
if (v___x_1645_ == 0)
{
if (v___x_1644_ == 0)
{
lean_dec(v_snd_1559_);
v_a_1620_ = v___x_1643_;
goto v___jp_1619_;
}
else
{
size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = lean_usize_of_nat(v___x_1642_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1559_, v___x_1646_, v___x_1647_, v___x_1643_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec(v_snd_1559_);
v___y_1632_ = v___x_1648_;
goto v___jp_1631_;
}
}
else
{
size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = lean_usize_of_nat(v___x_1642_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1559_, v___x_1649_, v___x_1650_, v___x_1643_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec(v_snd_1559_);
v___y_1632_ = v___x_1651_;
goto v___jp_1631_;
}
}
v___jp_1563_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_array_to_list(v___y_1564_);
v___x_1574_ = l_Lean_Elab_Tactic_tagUntaggedGoals(v_parentTag_1544_, v_tagSuffix_1545_, v___x_1573_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v___x_1574_, 0);
lean_dec(v_unused_1585_);
v___x_1576_ = v___x_1574_;
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v___x_1574_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___x_1573_);
v___x_1579_ = v___x_1561_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_fst_1558_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1573_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v___x_1573_);
lean_del_object(v___x_1561_);
lean_dec(v_fst_1558_);
v_a_1586_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1574_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1574_);
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
v___jp_1594_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1596_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec_ref(v_a_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref_known(v___x_1597_, 1);
v___y_1564_ = v___y_1595_;
v___y_1565_ = v_a_1547_;
v___y_1566_ = v_a_1548_;
v___y_1567_ = v_a_1549_;
v___y_1568_ = v_a_1550_;
v___y_1569_ = v_a_1551_;
v___y_1570_ = v_a_1552_;
v___y_1571_ = v_a_1553_;
v___y_1572_ = v_a_1554_;
goto v___jp_1563_;
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v___y_1595_);
lean_del_object(v___x_1561_);
lean_dec(v_fst_1558_);
lean_dec(v_tagSuffix_1545_);
lean_dec(v_parentTag_1544_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
v___jp_1606_:
{
if (lean_obj_tag(v___y_1608_) == 0)
{
lean_object* v_a_1609_; 
v_a_1609_ = lean_ctor_get(v___y_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___y_1608_, 1);
v___y_1595_ = v___y_1607_;
v_a_1596_ = v_a_1609_;
goto v___jp_1594_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v___y_1607_);
lean_del_object(v___x_1561_);
lean_dec(v_fst_1558_);
lean_dec(v_tagSuffix_1545_);
lean_dec(v_parentTag_1544_);
v_a_1610_ = lean_ctor_get(v___y_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___y_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___y_1608_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___y_1608_);
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
v___jp_1619_:
{
if (v_allowNaturalHoles_1546_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1621_ = lean_array_get_size(v_a_1620_);
v___x_1622_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1623_ = lean_nat_dec_lt(v___x_1618_, v___x_1621_);
if (v___x_1623_ == 0)
{
v___y_1595_ = v_a_1620_;
v_a_1596_ = v___x_1622_;
goto v___jp_1594_;
}
else
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_le(v___x_1621_, v___x_1621_);
if (v___x_1624_ == 0)
{
if (v___x_1623_ == 0)
{
v___y_1595_ = v_a_1620_;
v_a_1596_ = v___x_1622_;
goto v___jp_1594_;
}
else
{
size_t v___x_1625_; size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = lean_usize_of_nat(v___x_1621_);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1620_, v___x_1625_, v___x_1626_, v___x_1622_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
v___y_1607_ = v_a_1620_;
v___y_1608_ = v___x_1627_;
goto v___jp_1606_;
}
}
else
{
size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = lean_usize_of_nat(v___x_1621_);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1620_, v___x_1628_, v___x_1629_, v___x_1622_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
v___y_1607_ = v_a_1620_;
v___y_1608_ = v___x_1630_;
goto v___jp_1606_;
}
}
}
else
{
v___y_1564_ = v_a_1620_;
v___y_1565_ = v_a_1547_;
v___y_1566_ = v_a_1548_;
v___y_1567_ = v_a_1549_;
v___y_1568_ = v_a_1550_;
v___y_1569_ = v_a_1551_;
v___y_1570_ = v_a_1552_;
v___y_1571_ = v_a_1553_;
v___y_1572_ = v_a_1554_;
goto v___jp_1563_;
}
}
v___jp_1631_:
{
if (lean_obj_tag(v___y_1632_) == 0)
{
lean_object* v_a_1633_; 
v_a_1633_ = lean_ctor_get(v___y_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___y_1632_, 1);
v_a_1620_ = v_a_1633_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_del_object(v___x_1561_);
lean_dec(v_fst_1558_);
lean_dec(v_tagSuffix_1545_);
lean_dec(v_parentTag_1544_);
v_a_1634_ = lean_ctor_get(v___y_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___y_1632_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___y_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_tagSuffix_1545_);
lean_dec(v_parentTag_1544_);
v_a_1653_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1556_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1556_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* v_k_1661_, lean_object* v_parentTag_1662_, lean_object* v_tagSuffix_1663_, lean_object* v_allowNaturalHoles_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1674_; lean_object* v_res_1675_; 
v_allowNaturalHoles_boxed_1674_ = lean_unbox(v_allowNaturalHoles_1664_);
v_res_1675_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1661_, v_parentTag_1662_, v_tagSuffix_1663_, v_allowNaturalHoles_boxed_1674_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object* v_as_1676_, size_t v_i_1677_, size_t v_stop_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1676_, v_i_1677_, v_stop_1678_, v_b_1679_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object* v_as_1690_, lean_object* v_i_1691_, lean_object* v_stop_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
size_t v_i_boxed_1703_; size_t v_stop_boxed_1704_; lean_object* v_res_1705_; 
v_i_boxed_1703_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_stop_boxed_1704_ = lean_unbox_usize(v_stop_1692_);
lean_dec(v_stop_1692_);
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(v_as_1690_, v_i_boxed_1703_, v_stop_boxed_1704_, v_b_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec_ref(v_as_1690_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object* v_as_1706_, size_t v_i_1707_, size_t v_stop_1708_, lean_object* v_b_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1706_, v_i_1707_, v_stop_1708_, v_b_1709_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object* v_as_1720_, lean_object* v_i_1721_, lean_object* v_stop_1722_, lean_object* v_b_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
size_t v_i_boxed_1733_; size_t v_stop_boxed_1734_; lean_object* v_res_1735_; 
v_i_boxed_1733_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_stop_boxed_1734_ = lean_unbox_usize(v_stop_1722_);
lean_dec(v_stop_1722_);
v_res_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(v_as_1720_, v_i_boxed_1733_, v_stop_boxed_1734_, v_b_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v_as_1720_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object* v_mvarIds_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1736_, v___y_1738_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object* v_mvarIds_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(v_mvarIds_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object* v___x_1750_, lean_object* v_n_1751_, lean_object* v_as_1752_, lean_object* v_lo_1753_, lean_object* v_hi_1754_, lean_object* v_w_1755_, lean_object* v_hlo_1756_, lean_object* v_hhi_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1750_, v_n_1751_, v_as_1752_, v_lo_1753_, v_hi_1754_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1759_, lean_object* v_n_1760_, lean_object* v_as_1761_, lean_object* v_lo_1762_, lean_object* v_hi_1763_, lean_object* v_w_1764_, lean_object* v_hlo_1765_, lean_object* v_hhi_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(v___x_1759_, v_n_1760_, v_as_1761_, v_lo_1762_, v_hi_1763_, v_w_1764_, v_hlo_1765_, v_hhi_1766_);
lean_dec(v_hi_1763_);
lean_dec(v_n_1760_);
lean_dec_ref(v___x_1759_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1768_, lean_object* v_n_1769_, lean_object* v_lo_1770_, lean_object* v_hi_1771_, lean_object* v_hhi_1772_, lean_object* v_pivot_1773_, lean_object* v_as_1774_, lean_object* v_i_1775_, lean_object* v_k_1776_, lean_object* v_ilo_1777_, lean_object* v_ik_1778_, lean_object* v_w_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1768_, v_hi_1771_, v_pivot_1773_, v_as_1774_, v_i_1775_, v_k_1776_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1781_, lean_object* v_n_1782_, lean_object* v_lo_1783_, lean_object* v_hi_1784_, lean_object* v_hhi_1785_, lean_object* v_pivot_1786_, lean_object* v_as_1787_, lean_object* v_i_1788_, lean_object* v_k_1789_, lean_object* v_ilo_1790_, lean_object* v_ik_1791_, lean_object* v_w_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(v___x_1781_, v_n_1782_, v_lo_1783_, v_hi_1784_, v_hhi_1785_, v_pivot_1786_, v_as_1787_, v_i_1788_, v_k_1789_, v_ilo_1790_, v_ik_1791_, v_w_1792_);
lean_dec(v_hi_1784_);
lean_dec(v_lo_1783_);
lean_dec(v_n_1782_);
lean_dec_ref(v___x_1781_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object* v_k_1794_, lean_object* v_parentTag_1795_, lean_object* v_tagSuffix_1796_, uint8_t v_allowNaturalHoles_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
if (v_allowNaturalHoles_1797_ == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1794_, v_parentTag_1795_, v_tagSuffix_1796_, v_allowNaturalHoles_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1807_;
}
else
{
lean_object* v_declName_x3f_1808_; lean_object* v_macroStack_1809_; uint8_t v_mayPostpone_1810_; uint8_t v_errToSorry_1811_; lean_object* v_autoBoundImplicitContext_1812_; lean_object* v_autoBoundImplicitForbidden_1813_; lean_object* v_sectionVars_1814_; lean_object* v_sectionFVars_1815_; uint8_t v_implicitLambda_1816_; uint8_t v_heedElabAsElim_1817_; uint8_t v_isNoncomputableSection_1818_; uint8_t v_isMetaSection_1819_; uint8_t v_ignoreTCFailures_1820_; uint8_t v_inPattern_1821_; lean_object* v_tacSnap_x3f_1822_; uint8_t v_saveRecAppSyntax_1823_; uint8_t v_holesAsSyntheticOpaque_1824_; uint8_t v_checkDeprecated_1825_; lean_object* v_fixedTermElabs_1826_; uint8_t v___y_1828_; 
v_declName_x3f_1808_ = lean_ctor_get(v_a_1800_, 0);
v_macroStack_1809_ = lean_ctor_get(v_a_1800_, 1);
v_mayPostpone_1810_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8);
v_errToSorry_1811_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1812_ = lean_ctor_get(v_a_1800_, 2);
v_autoBoundImplicitForbidden_1813_ = lean_ctor_get(v_a_1800_, 3);
v_sectionVars_1814_ = lean_ctor_get(v_a_1800_, 4);
v_sectionFVars_1815_ = lean_ctor_get(v_a_1800_, 5);
v_implicitLambda_1816_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1817_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1818_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 4);
v_isMetaSection_1819_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1820_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 6);
v_inPattern_1821_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1822_ = lean_ctor_get(v_a_1800_, 6);
v_saveRecAppSyntax_1823_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1824_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 9);
v_checkDeprecated_1825_ = lean_ctor_get_uint8(v_a_1800_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1826_ = lean_ctor_get(v_a_1800_, 7);
if (v_holesAsSyntheticOpaque_1824_ == 0)
{
v___y_1828_ = v_allowNaturalHoles_1797_;
goto v___jp_1827_;
}
else
{
v___y_1828_ = v_holesAsSyntheticOpaque_1824_;
goto v___jp_1827_;
}
v___jp_1827_:
{
lean_object* v___x_1829_; uint8_t v_foApprox_1830_; uint8_t v_ctxApprox_1831_; uint8_t v_quasiPatternApprox_1832_; uint8_t v_constApprox_1833_; uint8_t v_isDefEqStuckEx_1834_; uint8_t v_unificationHints_1835_; uint8_t v_proofIrrelevance_1836_; uint8_t v_offsetCnstrs_1837_; uint8_t v_transparency_1838_; uint8_t v_etaStruct_1839_; uint8_t v_univApprox_1840_; uint8_t v_iota_1841_; uint8_t v_beta_1842_; uint8_t v_proj_1843_; uint8_t v_zeta_1844_; uint8_t v_zetaDelta_1845_; uint8_t v_zetaUnused_1846_; uint8_t v_zetaHave_1847_; uint8_t v_canUnfoldPredicateConfig_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1878_; 
v___x_1829_ = l_Lean_Meta_Context_config(v_a_1802_);
v_foApprox_1830_ = lean_ctor_get_uint8(v___x_1829_, 0);
v_ctxApprox_1831_ = lean_ctor_get_uint8(v___x_1829_, 1);
v_quasiPatternApprox_1832_ = lean_ctor_get_uint8(v___x_1829_, 2);
v_constApprox_1833_ = lean_ctor_get_uint8(v___x_1829_, 3);
v_isDefEqStuckEx_1834_ = lean_ctor_get_uint8(v___x_1829_, 4);
v_unificationHints_1835_ = lean_ctor_get_uint8(v___x_1829_, 5);
v_proofIrrelevance_1836_ = lean_ctor_get_uint8(v___x_1829_, 6);
v_offsetCnstrs_1837_ = lean_ctor_get_uint8(v___x_1829_, 8);
v_transparency_1838_ = lean_ctor_get_uint8(v___x_1829_, 9);
v_etaStruct_1839_ = lean_ctor_get_uint8(v___x_1829_, 10);
v_univApprox_1840_ = lean_ctor_get_uint8(v___x_1829_, 11);
v_iota_1841_ = lean_ctor_get_uint8(v___x_1829_, 12);
v_beta_1842_ = lean_ctor_get_uint8(v___x_1829_, 13);
v_proj_1843_ = lean_ctor_get_uint8(v___x_1829_, 14);
v_zeta_1844_ = lean_ctor_get_uint8(v___x_1829_, 15);
v_zetaDelta_1845_ = lean_ctor_get_uint8(v___x_1829_, 16);
v_zetaUnused_1846_ = lean_ctor_get_uint8(v___x_1829_, 17);
v_zetaHave_1847_ = lean_ctor_get_uint8(v___x_1829_, 18);
v_canUnfoldPredicateConfig_1848_ = lean_ctor_get_uint8(v___x_1829_, 19);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1850_ = v___x_1829_;
v_isShared_1851_ = v_isSharedCheck_1878_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v___x_1829_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1878_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
uint8_t v_trackZetaDelta_1852_; lean_object* v_zetaDeltaSet_1853_; lean_object* v_lctx_1854_; lean_object* v_localInstances_1855_; lean_object* v_defEqCtx_x3f_1856_; lean_object* v_synthPendingDepth_1857_; lean_object* v_customCanUnfoldPredicate_x3f_1858_; uint8_t v_univApprox_1859_; uint8_t v_inTypeClassResolution_1860_; uint8_t v_cacheInferType_1861_; lean_object* v___x_1863_; 
v_trackZetaDelta_1852_ = lean_ctor_get_uint8(v_a_1802_, sizeof(void*)*7);
v_zetaDeltaSet_1853_ = lean_ctor_get(v_a_1802_, 1);
v_lctx_1854_ = lean_ctor_get(v_a_1802_, 2);
v_localInstances_1855_ = lean_ctor_get(v_a_1802_, 3);
v_defEqCtx_x3f_1856_ = lean_ctor_get(v_a_1802_, 4);
v_synthPendingDepth_1857_ = lean_ctor_get(v_a_1802_, 5);
v_customCanUnfoldPredicate_x3f_1858_ = lean_ctor_get(v_a_1802_, 6);
v_univApprox_1859_ = lean_ctor_get_uint8(v_a_1802_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1860_ = lean_ctor_get_uint8(v_a_1802_, sizeof(void*)*7 + 2);
v_cacheInferType_1861_ = lean_ctor_get_uint8(v_a_1802_, sizeof(void*)*7 + 3);
if (v_isShared_1851_ == 0)
{
v___x_1863_ = v___x_1850_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 0, v_foApprox_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 1, v_ctxApprox_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 2, v_quasiPatternApprox_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 3, v_constApprox_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 4, v_isDefEqStuckEx_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 5, v_unificationHints_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 6, v_proofIrrelevance_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 8, v_offsetCnstrs_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 9, v_transparency_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 10, v_etaStruct_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 11, v_univApprox_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 12, v_iota_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 13, v_beta_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 14, v_proj_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 15, v_zeta_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 16, v_zetaDelta_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 17, v_zetaUnused_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 18, v_zetaHave_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, 19, v_canUnfoldPredicateConfig_1848_);
v___x_1863_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
uint64_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_ctor_set_uint8(v___x_1863_, 7, v_allowNaturalHoles_1797_);
v___x_1864_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1863_);
lean_inc_ref(v_fixedTermElabs_1826_);
lean_inc(v_tacSnap_x3f_1822_);
lean_inc(v_sectionFVars_1815_);
lean_inc(v_sectionVars_1814_);
lean_inc_ref(v_autoBoundImplicitForbidden_1813_);
lean_inc(v_autoBoundImplicitContext_1812_);
lean_inc(v_macroStack_1809_);
lean_inc(v_declName_x3f_1808_);
v___x_1865_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1865_, 0, v_declName_x3f_1808_);
lean_ctor_set(v___x_1865_, 1, v_macroStack_1809_);
lean_ctor_set(v___x_1865_, 2, v_autoBoundImplicitContext_1812_);
lean_ctor_set(v___x_1865_, 3, v_autoBoundImplicitForbidden_1813_);
lean_ctor_set(v___x_1865_, 4, v_sectionVars_1814_);
lean_ctor_set(v___x_1865_, 5, v_sectionFVars_1815_);
lean_ctor_set(v___x_1865_, 6, v_tacSnap_x3f_1822_);
lean_ctor_set(v___x_1865_, 7, v_fixedTermElabs_1826_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8, v_mayPostpone_1810_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 1, v_errToSorry_1811_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 2, v_implicitLambda_1816_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 3, v_heedElabAsElim_1817_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1818_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 5, v_isMetaSection_1819_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1820_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 7, v_inPattern_1821_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1823_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 9, v___y_1828_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*8 + 10, v_checkDeprecated_1825_);
v___x_1866_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1866_, 0, v___x_1863_);
lean_ctor_set_uint64(v___x_1866_, sizeof(void*)*1, v___x_1864_);
lean_inc(v_customCanUnfoldPredicate_x3f_1858_);
lean_inc(v_synthPendingDepth_1857_);
lean_inc(v_defEqCtx_x3f_1856_);
lean_inc_ref(v_localInstances_1855_);
lean_inc_ref(v_lctx_1854_);
lean_inc(v_zetaDeltaSet_1853_);
v___x_1867_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v_zetaDeltaSet_1853_);
lean_ctor_set(v___x_1867_, 2, v_lctx_1854_);
lean_ctor_set(v___x_1867_, 3, v_localInstances_1855_);
lean_ctor_set(v___x_1867_, 4, v_defEqCtx_x3f_1856_);
lean_ctor_set(v___x_1867_, 5, v_synthPendingDepth_1857_);
lean_ctor_set(v___x_1867_, 6, v_customCanUnfoldPredicate_x3f_1858_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*7, v_trackZetaDelta_1852_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*7 + 1, v_univApprox_1859_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1860_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*7 + 3, v_cacheInferType_1861_);
v___x_1868_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1794_, v_parentTag_1795_, v_tagSuffix_1796_, v_allowNaturalHoles_1797_, v_a_1798_, v_a_1799_, v___x_1865_, v_a_1801_, v___x_1867_, v_a_1803_, v_a_1804_, v_a_1805_);
lean_dec_ref_known(v___x_1867_, 7);
lean_dec_ref_known(v___x_1865_, 8);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
return v___x_1868_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object* v_k_1879_, lean_object* v_parentTag_1880_, lean_object* v_tagSuffix_1881_, lean_object* v_allowNaturalHoles_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1892_; lean_object* v_res_1893_; 
v_allowNaturalHoles_boxed_1892_ = lean_unbox(v_allowNaturalHoles_1882_);
v_res_1893_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v_k_1879_, v_parentTag_1880_, v_tagSuffix_1881_, v_allowNaturalHoles_boxed_1892_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* v_stx_1894_, lean_object* v_expectedType_x3f_1895_, lean_object* v_tagSuffix_1896_, uint8_t v_allowNaturalHoles_1897_, lean_object* v_parentTag_x3f_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_a_1909_; 
if (lean_obj_tag(v_parentTag_x3f_1898_) == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Elab_Tactic_getMainTag___redArg(v_a_1900_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v_a_1909_ = v_a_1915_;
goto v___jp_1908_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_tagSuffix_1896_);
lean_dec(v_expectedType_x3f_1895_);
lean_dec(v_stx_1894_);
v_a_1916_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1914_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_val_1924_; 
v_val_1924_ = lean_ctor_get(v_parentTag_x3f_1898_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v_parentTag_x3f_1898_, 1);
v_a_1909_ = v_val_1924_;
goto v___jp_1908_;
}
v___jp_1908_:
{
uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1910_ = 0;
v___x_1911_ = lean_box(v___x_1910_);
v___x_1912_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(v___x_1912_, 0, v_stx_1894_);
lean_closure_set(v___x_1912_, 1, v_expectedType_x3f_1895_);
lean_closure_set(v___x_1912_, 2, v___x_1911_);
v___x_1913_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_1912_, v_a_1909_, v_tagSuffix_1896_, v_allowNaturalHoles_1897_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* v_stx_1925_, lean_object* v_expectedType_x3f_1926_, lean_object* v_tagSuffix_1927_, lean_object* v_allowNaturalHoles_1928_, lean_object* v_parentTag_x3f_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1939_; lean_object* v_res_1940_; 
v_allowNaturalHoles_boxed_1939_ = lean_unbox(v_allowNaturalHoles_1928_);
v_res_1940_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_1925_, v_expectedType_x3f_1926_, v_tagSuffix_1927_, v_allowNaturalHoles_boxed_1939_, v_parentTag_x3f_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
return v_res_1940_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object* v_a_1941_, lean_object* v_x_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_instBEqMVarId_beq(v_x_1942_, v_a_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object* v_a_1944_, lean_object* v_x_1945_){
_start:
{
uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = l_Lean_Elab_Tactic_refineCore___lam__0(v_a_1944_, v_x_1945_);
lean_dec(v_x_1945_);
lean_dec(v_a_1944_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v_ks_1952_; lean_object* v_vs_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1977_; 
v_ks_1952_ = lean_ctor_get(v_x_1948_, 0);
v_vs_1953_ = lean_ctor_get(v_x_1948_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1948_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1955_ = v_x_1948_;
v_isShared_1956_ = v_isSharedCheck_1977_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_vs_1953_);
lean_inc(v_ks_1952_);
lean_dec(v_x_1948_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1977_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = lean_array_get_size(v_ks_1952_);
v___x_1958_ = lean_nat_dec_lt(v_x_1949_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec(v_x_1949_);
v___x_1959_ = lean_array_push(v_ks_1952_, v_x_1950_);
v___x_1960_ = lean_array_push(v_vs_1953_, v_x_1951_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v___x_1960_);
lean_ctor_set(v___x_1955_, 0, v___x_1959_);
v___x_1962_ = v___x_1955_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
lean_object* v_k_x27_1964_; uint8_t v___x_1965_; 
v_k_x27_1964_ = lean_array_fget_borrowed(v_ks_1952_, v_x_1949_);
v___x_1965_ = l_Lean_instBEqMVarId_beq(v_x_1950_, v_k_x27_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; 
if (v_isShared_1956_ == 0)
{
v___x_1967_ = v___x_1955_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_ks_1952_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_vs_1953_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_nat_add(v_x_1949_, v___x_1968_);
lean_dec(v_x_1949_);
v_x_1948_ = v___x_1967_;
v_x_1949_ = v___x_1969_;
goto _start;
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = lean_array_fset(v_ks_1952_, v_x_1949_, v_x_1950_);
v___x_1973_ = lean_array_fset(v_vs_1953_, v_x_1949_, v_x_1951_);
lean_dec(v_x_1949_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v___x_1973_);
lean_ctor_set(v___x_1955_, 0, v___x_1972_);
v___x_1975_ = v___x_1955_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_1978_, lean_object* v_k_1979_, lean_object* v_v_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_1978_, v___x_1981_, v_k_1979_, v_v_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1984_, size_t v_x_1985_, size_t v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_object* v_es_1989_; size_t v___x_1990_; size_t v___x_1991_; lean_object* v_j_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_es_1989_ = lean_ctor_get(v_x_1984_, 0);
v___x_1990_ = ((size_t)31ULL);
v___x_1991_ = lean_usize_land(v_x_1985_, v___x_1990_);
v_j_1992_ = lean_usize_to_nat(v___x_1991_);
v___x_1993_ = lean_array_get_size(v_es_1989_);
v___x_1994_ = lean_nat_dec_lt(v_j_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec(v_j_1992_);
lean_dec(v_x_1988_);
lean_dec(v_x_1987_);
return v_x_1984_;
}
else
{
lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2033_; 
lean_inc_ref(v_es_1989_);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v_x_1984_, 0);
lean_dec(v_unused_2034_);
v___x_1996_ = v_x_1984_;
v_isShared_1997_ = v_isSharedCheck_2033_;
goto v_resetjp_1995_;
}
else
{
lean_dec(v_x_1984_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2033_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_v_1998_; lean_object* v___x_1999_; lean_object* v_xs_x27_2000_; lean_object* v___y_2002_; 
v_v_1998_ = lean_array_fget(v_es_1989_, v_j_1992_);
v___x_1999_ = lean_box(0);
v_xs_x27_2000_ = lean_array_fset(v_es_1989_, v_j_1992_, v___x_1999_);
switch(lean_obj_tag(v_v_1998_))
{
case 0:
{
lean_object* v_key_2007_; lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2018_; 
v_key_2007_ = lean_ctor_get(v_v_1998_, 0);
v_val_2008_ = lean_ctor_get(v_v_1998_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_v_1998_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2010_ = v_v_1998_;
v_isShared_2011_ = v_isSharedCheck_2018_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_inc(v_key_2007_);
lean_dec(v_v_1998_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2018_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_instBEqMVarId_beq(v_x_1987_, v_key_2007_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_del_object(v___x_2010_);
v___x_2013_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2007_, v_val_2008_, v_x_1987_, v_x_1988_);
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
v___y_2002_ = v___x_2014_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2016_; 
lean_dec(v_val_2008_);
lean_dec(v_key_2007_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_x_1988_);
lean_ctor_set(v___x_2010_, 0, v_x_1987_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_x_1987_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_x_1988_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v___y_2002_ = v___x_2016_;
goto v___jp_2001_;
}
}
}
}
case 1:
{
lean_object* v_node_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2031_; 
v_node_2019_ = lean_ctor_get(v_v_1998_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_v_1998_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2021_ = v_v_1998_;
v_isShared_2022_ = v_isSharedCheck_2031_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_node_2019_);
lean_dec(v_v_1998_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2031_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
size_t v___x_2023_; size_t v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2023_ = ((size_t)5ULL);
v___x_2024_ = lean_usize_shift_right(v_x_1985_, v___x_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_x_1986_, v___x_2025_);
v___x_2027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_node_2019_, v___x_2024_, v___x_2026_, v_x_1987_, v_x_1988_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2027_);
v___x_2029_ = v___x_2021_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
v___y_2002_ = v___x_2029_;
goto v___jp_2001_;
}
}
}
default: 
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_x_1987_);
lean_ctor_set(v___x_2032_, 1, v_x_1988_);
v___y_2002_ = v___x_2032_;
goto v___jp_2001_;
}
}
v___jp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_array_fset(v_xs_x27_2000_, v_j_1992_, v___y_2002_);
lean_dec(v_j_1992_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2003_);
v___x_2005_ = v___x_1996_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
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
else
{
lean_object* v_ks_2035_; lean_object* v_vs_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2054_; 
v_ks_2035_ = lean_ctor_get(v_x_1984_, 0);
v_vs_2036_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2038_ = v_x_1984_;
v_isShared_2039_ = v_isSharedCheck_2054_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_vs_2036_);
lean_inc(v_ks_2035_);
lean_dec(v_x_1984_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2054_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_ks_2035_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_vs_2036_);
v___x_2041_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v_newNode_2042_; size_t v___x_2043_; uint8_t v___x_2044_; 
v_newNode_2042_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_2041_, v_x_1987_, v_x_1988_);
v___x_2043_ = ((size_t)7ULL);
v___x_2044_ = lean_usize_dec_le(v___x_2043_, v_x_1986_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2042_);
v___x_2046_ = lean_unsigned_to_nat(4u);
v___x_2047_ = lean_nat_dec_lt(v___x_2045_, v___x_2046_);
lean_dec(v___x_2045_);
if (v___x_2047_ == 0)
{
lean_object* v_ks_2048_; lean_object* v_vs_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_ks_2048_ = lean_ctor_get(v_newNode_2042_, 0);
lean_inc_ref(v_ks_2048_);
v_vs_2049_ = lean_ctor_get(v_newNode_2042_, 1);
lean_inc_ref(v_vs_2049_);
lean_dec_ref(v_newNode_2042_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2052_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1986_, v_ks_2048_, v_vs_2049_, v___x_2050_, v___x_2051_);
lean_dec_ref(v_vs_2049_);
lean_dec_ref(v_ks_2048_);
return v___x_2052_;
}
else
{
return v_newNode_2042_;
}
}
else
{
return v_newNode_2042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_2055_, lean_object* v_keys_2056_, lean_object* v_vals_2057_, lean_object* v_i_2058_, lean_object* v_entries_2059_){
_start:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = lean_array_get_size(v_keys_2056_);
v___x_2061_ = lean_nat_dec_lt(v_i_2058_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec(v_i_2058_);
return v_entries_2059_;
}
else
{
lean_object* v_k_2062_; lean_object* v_v_2063_; uint64_t v___x_2064_; size_t v_h_2065_; size_t v___x_2066_; lean_object* v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; size_t v_h_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_k_2062_ = lean_array_fget_borrowed(v_keys_2056_, v_i_2058_);
v_v_2063_ = lean_array_fget_borrowed(v_vals_2057_, v_i_2058_);
v___x_2064_ = l_Lean_instHashableMVarId_hash(v_k_2062_);
v_h_2065_ = lean_uint64_to_usize(v___x_2064_);
v___x_2066_ = ((size_t)5ULL);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = ((size_t)1ULL);
v___x_2069_ = lean_usize_sub(v_depth_2055_, v___x_2068_);
v___x_2070_ = lean_usize_mul(v___x_2066_, v___x_2069_);
v_h_2071_ = lean_usize_shift_right(v_h_2065_, v___x_2070_);
v___x_2072_ = lean_nat_add(v_i_2058_, v___x_2067_);
lean_dec(v_i_2058_);
lean_inc(v_v_2063_);
lean_inc(v_k_2062_);
v___x_2073_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_entries_2059_, v_h_2071_, v_depth_2055_, v_k_2062_, v_v_2063_);
v_i_2058_ = v___x_2072_;
v_entries_2059_ = v___x_2073_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_2075_, lean_object* v_keys_2076_, lean_object* v_vals_2077_, lean_object* v_i_2078_, lean_object* v_entries_2079_){
_start:
{
size_t v_depth_boxed_2080_; lean_object* v_res_2081_; 
v_depth_boxed_2080_ = lean_unbox_usize(v_depth_2075_);
lean_dec(v_depth_2075_);
v_res_2081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_2080_, v_keys_2076_, v_vals_2077_, v_i_2078_, v_entries_2079_);
lean_dec_ref(v_vals_2077_);
lean_dec_ref(v_keys_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
size_t v_x_3308__boxed_2087_; size_t v_x_3309__boxed_2088_; lean_object* v_res_2089_; 
v_x_3308__boxed_2087_ = lean_unbox_usize(v_x_2083_);
lean_dec(v_x_2083_);
v_x_3309__boxed_2088_ = lean_unbox_usize(v_x_2084_);
lean_dec(v_x_2084_);
v_res_2089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2082_, v_x_3308__boxed_2087_, v_x_3309__boxed_2088_, v_x_2085_, v_x_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_){
_start:
{
uint64_t v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2093_ = l_Lean_instHashableMVarId_hash(v_x_2091_);
v___x_2094_ = lean_uint64_to_usize(v___x_2093_);
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2090_, v___x_2094_, v___x_2095_, v_x_2091_, v_x_2092_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object* v_mvarId_2097_, lean_object* v_val_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v_mctx_2102_; lean_object* v_cache_2103_; lean_object* v_zetaDeltaFVarIds_2104_; lean_object* v_postponed_2105_; lean_object* v_diag_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2135_; 
v___x_2101_ = lean_st_ref_take(v___y_2099_);
v_mctx_2102_ = lean_ctor_get(v___x_2101_, 0);
v_cache_2103_ = lean_ctor_get(v___x_2101_, 1);
v_zetaDeltaFVarIds_2104_ = lean_ctor_get(v___x_2101_, 2);
v_postponed_2105_ = lean_ctor_get(v___x_2101_, 3);
v_diag_2106_ = lean_ctor_get(v___x_2101_, 4);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2108_ = v___x_2101_;
v_isShared_2109_ = v_isSharedCheck_2135_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_diag_2106_);
lean_inc(v_postponed_2105_);
lean_inc(v_zetaDeltaFVarIds_2104_);
lean_inc(v_cache_2103_);
lean_inc(v_mctx_2102_);
lean_dec(v___x_2101_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2135_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_depth_2110_; lean_object* v_levelAssignDepth_2111_; lean_object* v_lmvarCounter_2112_; lean_object* v_mvarCounter_2113_; lean_object* v_lDecls_2114_; lean_object* v_decls_2115_; lean_object* v_userNames_2116_; lean_object* v_lAssignment_2117_; lean_object* v_eAssignment_2118_; lean_object* v_dAssignment_2119_; lean_object* v_instanceTypedMVars_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2134_; 
v_depth_2110_ = lean_ctor_get(v_mctx_2102_, 0);
v_levelAssignDepth_2111_ = lean_ctor_get(v_mctx_2102_, 1);
v_lmvarCounter_2112_ = lean_ctor_get(v_mctx_2102_, 2);
v_mvarCounter_2113_ = lean_ctor_get(v_mctx_2102_, 3);
v_lDecls_2114_ = lean_ctor_get(v_mctx_2102_, 4);
v_decls_2115_ = lean_ctor_get(v_mctx_2102_, 5);
v_userNames_2116_ = lean_ctor_get(v_mctx_2102_, 6);
v_lAssignment_2117_ = lean_ctor_get(v_mctx_2102_, 7);
v_eAssignment_2118_ = lean_ctor_get(v_mctx_2102_, 8);
v_dAssignment_2119_ = lean_ctor_get(v_mctx_2102_, 9);
v_instanceTypedMVars_2120_ = lean_ctor_get(v_mctx_2102_, 10);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_mctx_2102_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2122_ = v_mctx_2102_;
v_isShared_2123_ = v_isSharedCheck_2134_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_instanceTypedMVars_2120_);
lean_inc(v_dAssignment_2119_);
lean_inc(v_eAssignment_2118_);
lean_inc(v_lAssignment_2117_);
lean_inc(v_userNames_2116_);
lean_inc(v_decls_2115_);
lean_inc(v_lDecls_2114_);
lean_inc(v_mvarCounter_2113_);
lean_inc(v_lmvarCounter_2112_);
lean_inc(v_levelAssignDepth_2111_);
lean_inc(v_depth_2110_);
lean_dec(v_mctx_2102_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2134_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_eAssignment_2118_, v_mvarId_2097_, v_val_2098_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 8, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_depth_2110_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_levelAssignDepth_2111_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_lmvarCounter_2112_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_mvarCounter_2113_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_lDecls_2114_);
lean_ctor_set(v_reuseFailAlloc_2133_, 5, v_decls_2115_);
lean_ctor_set(v_reuseFailAlloc_2133_, 6, v_userNames_2116_);
lean_ctor_set(v_reuseFailAlloc_2133_, 7, v_lAssignment_2117_);
lean_ctor_set(v_reuseFailAlloc_2133_, 8, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2133_, 9, v_dAssignment_2119_);
lean_ctor_set(v_reuseFailAlloc_2133_, 10, v_instanceTypedMVars_2120_);
v___x_2126_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2126_);
v___x_2128_ = v___x_2108_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_cache_2103_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_zetaDeltaFVarIds_2104_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_postponed_2105_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_diag_2106_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_st_ref_put(v___y_2099_, v___x_2128_);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object* v_mvarId_2136_, lean_object* v_val_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2136_, v_val_2137_, v___y_2138_);
lean_dec(v___y_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(lean_object* v_msgData_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; lean_object* v_env_2148_; lean_object* v___x_2149_; lean_object* v_mctx_2150_; lean_object* v_lctx_2151_; lean_object* v_options_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2147_ = lean_st_ref_get(v___y_2145_);
v_env_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc_ref(v_env_2148_);
lean_dec(v___x_2147_);
v___x_2149_ = lean_st_ref_get(v___y_2143_);
v_mctx_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc_ref(v_mctx_2150_);
lean_dec(v___x_2149_);
v_lctx_2151_ = lean_ctor_get(v___y_2142_, 2);
v_options_2152_ = lean_ctor_get(v___y_2144_, 1);
lean_inc_ref(v_options_2152_);
lean_inc_ref(v_lctx_2151_);
v___x_2153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2153_, 0, v_env_2148_);
lean_ctor_set(v___x_2153_, 1, v_mctx_2150_);
lean_ctor_set(v___x_2153_, 2, v_lctx_2151_);
lean_ctor_set(v___x_2153_, 3, v_options_2152_);
v___x_2154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v_msgData_2141_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(lean_object* v_msgData_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msgData_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(lean_object* v_msg_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_ref_2169_; lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2179_; 
v_ref_2169_ = lean_ctor_get(v___y_2166_, 4);
v___x_2170_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_inc(v_ref_2169_);
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v_ref_2169_);
lean_ctor_set(v___x_2175_, 1, v_a_2171_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 1);
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2186_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__0));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__2));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__4));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object* v_stx_2196_, lean_object* v_tagSuffix_2197_, uint8_t v_allowNaturalHoles_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Elab_Tactic_getMainTarget(v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2209_);
v___x_2211_ = lean_box(0);
v___x_2212_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_2196_, v___x_2210_, v_tagSuffix_2197_, v_allowNaturalHoles_2198_, v___x_2211_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v_fst_2214_; lean_object* v_snd_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2261_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v_fst_2214_ = lean_ctor_get(v_a_2213_, 0);
v_snd_2215_ = lean_ctor_get(v_a_2213_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_a_2213_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2217_ = v_a_2213_;
v_isShared_2218_ = v_isSharedCheck_2261_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_snd_2215_);
lean_inc(v_fst_2214_);
lean_dec(v_a_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2261_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2200_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v_a_2222_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___x_2234_; uint8_t v___x_2248_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc_n(v_a_2220_, 2);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_fst_2214_, v___y_2204_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
v___x_2234_ = l_Lean_mkMVar(v_a_2220_);
v___x_2248_ = lean_expr_eqv(v_a_2222_, v___x_2234_);
if (v___x_2248_ == 0)
{
lean_object* v___f_2249_; lean_object* v___x_2250_; 
lean_inc(v_a_2220_);
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2249_, 0, v_a_2220_);
lean_inc(v_a_2222_);
v___x_2250_ = l_Lean_FindMVar_main(v___f_2249_, v_a_2222_, v___x_2211_);
if (lean_obj_tag(v___x_2250_) == 1)
{
lean_dec_ref_known(v___x_2250_, 1);
lean_dec(v_a_2220_);
lean_dec(v_snd_2215_);
goto v___jp_2235_;
}
else
{
lean_dec(v___x_2250_);
if (v___x_2248_ == 0)
{
lean_dec_ref(v___x_2234_);
lean_del_object(v___x_2217_);
v___y_2224_ = v___y_2199_;
v___y_2225_ = v___y_2200_;
v___y_2226_ = v___y_2201_;
v___y_2227_ = v___y_2202_;
v___y_2228_ = v___y_2203_;
v___y_2229_ = v___y_2204_;
v___y_2230_ = v___y_2205_;
v___y_2231_ = v___y_2206_;
goto v___jp_2223_;
}
else
{
lean_dec(v_a_2220_);
lean_dec(v_snd_2215_);
goto v___jp_2235_;
}
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v___x_2234_);
lean_dec(v_a_2222_);
lean_del_object(v___x_2217_);
v___x_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_a_2220_);
lean_ctor_set(v___x_2251_, 1, v_snd_2215_);
v___x_2252_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2251_, v___y_2200_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2252_;
}
v___jp_2223_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_a_2220_, v_a_2222_, v___y_2229_);
lean_dec_ref(v___x_2232_);
v___x_2233_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_2215_, v___y_2225_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
return v___x_2233_;
}
v___jp_2235_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__1, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1);
v___x_2237_ = l_Lean_indentExpr(v_a_2222_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set_tag(v___x_2217_, 7);
lean_ctor_set(v___x_2217_, 1, v___x_2237_);
lean_ctor_set(v___x_2217_, 0, v___x_2236_);
v___x_2239_ = v___x_2217_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2240_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__3, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = l_Lean_MessageData_ofExpr(v___x_2234_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2245_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_del_object(v___x_2217_);
lean_dec(v_snd_2215_);
lean_dec(v_fst_2214_);
v_a_2253_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2219_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2219_);
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
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2212_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2212_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_tagSuffix_2197_);
lean_dec(v_stx_2196_);
v_a_2270_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2208_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2208_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object* v_stx_2278_, lean_object* v_tagSuffix_2279_, lean_object* v_allowNaturalHoles_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2290_; lean_object* v_res_2291_; 
v_allowNaturalHoles_boxed_2290_ = lean_unbox(v_allowNaturalHoles_2280_);
v_res_2291_ = l_Lean_Elab_Tactic_refineCore___lam__1(v_stx_2278_, v_tagSuffix_2279_, v_allowNaturalHoles_boxed_2290_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object* v_stx_2292_, lean_object* v_tagSuffix_2293_, uint8_t v_allowNaturalHoles_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_box(v_allowNaturalHoles_2294_);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2305_, 0, v_stx_2292_);
lean_closure_set(v___f_2305_, 1, v_tagSuffix_2293_);
lean_closure_set(v___f_2305_, 2, v___x_2304_);
v___x_2306_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2305_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object* v_stx_2307_, lean_object* v_tagSuffix_2308_, lean_object* v_allowNaturalHoles_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2319_; lean_object* v_res_2320_; 
v_allowNaturalHoles_boxed_2319_ = lean_unbox(v_allowNaturalHoles_2309_);
v_res_2320_ = l_Lean_Elab_Tactic_refineCore(v_stx_2307_, v_tagSuffix_2308_, v_allowNaturalHoles_boxed_2319_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(lean_object* v_mvarId_2321_, lean_object* v_val_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2321_, v_val_2322_, v___y_2328_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object* v_mvarId_2333_, lean_object* v_val_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(v_mvarId_2333_, v_val_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(lean_object* v_00_u03b1_2345_, lean_object* v_msg_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2346_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(lean_object* v_00_u03b1_2357_, lean_object* v_msg_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(v_00_u03b1_2357_, v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(lean_object* v_00_u03b2_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_x_2370_, v_x_2371_, v_x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2374_, lean_object* v_x_2375_, size_t v_x_2376_, size_t v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2375_, v_x_2376_, v_x_2377_, v_x_2378_, v_x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_){
_start:
{
size_t v_x_3854__boxed_2387_; size_t v_x_3855__boxed_2388_; lean_object* v_res_2389_; 
v_x_3854__boxed_2387_ = lean_unbox_usize(v_x_2383_);
lean_dec(v_x_2383_);
v_x_3855__boxed_2388_ = lean_unbox_usize(v_x_2384_);
lean_dec(v_x_2384_);
v_res_2389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(v_00_u03b2_2381_, v_x_2382_, v_x_3854__boxed_2387_, v_x_3855__boxed_2388_, v_x_2385_, v_x_2386_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2390_, lean_object* v_n_2391_, lean_object* v_k_2392_, lean_object* v_v_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_2391_, v_k_2392_, v_v_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2395_, size_t v_depth_2396_, lean_object* v_keys_2397_, lean_object* v_vals_2398_, lean_object* v_heq_2399_, lean_object* v_i_2400_, lean_object* v_entries_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_2396_, v_keys_2397_, v_vals_2398_, v_i_2400_, v_entries_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2403_, lean_object* v_depth_2404_, lean_object* v_keys_2405_, lean_object* v_vals_2406_, lean_object* v_heq_2407_, lean_object* v_i_2408_, lean_object* v_entries_2409_){
_start:
{
size_t v_depth_boxed_2410_; lean_object* v_res_2411_; 
v_depth_boxed_2410_ = lean_unbox_usize(v_depth_2404_);
lean_dec(v_depth_2404_);
v_res_2411_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_2403_, v_depth_boxed_2410_, v_keys_2405_, v_vals_2406_, v_heq_2407_, v_i_2408_, v_entries_2409_);
lean_dec_ref(v_vals_2406_);
lean_dec_ref(v_keys_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_, lean_object* v_x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_2413_, v_x_2414_, v_x_2415_, v_x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object* v_stx_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
lean_inc(v_stx_2426_);
v___x_2437_ = l_Lean_Syntax_isOfKind(v_stx_2426_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_dec(v_stx_2426_);
v___x_2438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = l_Lean_Syntax_getArg(v_stx_2426_, v___x_2439_);
lean_dec(v_stx_2426_);
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__2));
v___x_2442_ = 0;
v___x_2443_ = l_Lean_Elab_Tactic_refineCore(v___x_2440_, v___x_2441_, v___x_2442_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___boxed(lean_object* v_stx_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Elab_Tactic_evalRefine(v_stx_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2462_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2463_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
v___x_2464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2465_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine___boxed), 10, 0);
v___x_2466_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2462_, v___x_2463_, v___x_2464_, v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6));
v___x_2497_ = l_Lean_addBuiltinDeclarationRanges(v___x_2495_, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object* v_stx_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
lean_inc(v_stx_2508_);
v___x_2519_ = l_Lean_Syntax_isOfKind(v_stx_2508_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec(v_stx_2508_);
v___x_2520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2521_ = lean_unsigned_to_nat(1u);
v___x_2522_ = l_Lean_Syntax_getArg(v_stx_2508_, v___x_2521_);
lean_dec(v_stx_2508_);
v___x_2523_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__2));
v___x_2524_ = l_Lean_Elab_Tactic_refineCore(v___x_2522_, v___x_2523_, v___x_2519_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___boxed(lean_object* v_stx_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_Elab_Tactic_evalRefine_x27(v_stx_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2543_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
v___x_2545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2546_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine_x27___boxed), 10, 0);
v___x_2547_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2543_, v___x_2544_, v___x_2545_, v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6));
v___x_2578_ = l_Lean_addBuiltinDeclarationRanges(v___x_2576_, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
return v_res_2580_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0));
v___x_2583_ = l_Lean_stringToMessageData(v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t v___x_2584_, lean_object* v_stx_2585_, lean_object* v___x_2586_, uint8_t v___x_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
if (v___x_2584_ == 0)
{
lean_object* v___x_2597_; 
lean_dec_ref(v___x_2586_);
v___x_2597_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2597_;
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2598_ = lean_unsigned_to_nat(1u);
v___x_2599_ = l_Lean_Syntax_getArg(v_stx_2585_, v___x_2598_);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Name_mkStr1(v___x_2586_);
v___x_2602_ = l_Lean_Elab_Tactic_elabTermWithHoles(v___x_2599_, v___x_2600_, v___x_2601_, v___x_2587_, v___x_2600_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_fst_2604_; lean_object* v_snd_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2653_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v_fst_2604_ = lean_ctor_get(v_a_2603_, 0);
v_snd_2605_ = lean_ctor_get(v_a_2603_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_a_2603_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2607_ = v_a_2603_;
v_isShared_2608_ = v_isSharedCheck_2653_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_snd_2605_);
lean_inc(v_fst_2604_);
lean_dec(v_a_2603_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2653_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = l_Lean_Expr_getLambdaBody(v_fst_2604_);
v___x_2610_ = l_Lean_Expr_getAppFn(v___x_2609_);
lean_dec_ref(v___x_2609_);
if (lean_obj_tag(v___x_2610_) == 1)
{
lean_object* v_fvarId_2611_; lean_object* v___x_2612_; 
v_fvarId_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_fvarId_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2589_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
lean_inc(v___y_2595_);
lean_inc_ref(v___y_2594_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v_fst_2604_);
v___x_2614_ = lean_infer_type(v_fst_2604_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = l_Lean_Expr_headBeta(v_a_2615_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
v___x_2618_ = l_Lean_MVarId_replace(v_a_2613_, v_fvarId_2611_, v_fst_2604_, v___x_2617_, v___x_2600_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_mvarId_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v_mvarId_2620_ = lean_ctor_get(v_a_2619_, 1);
lean_inc(v_mvarId_2620_);
lean_dec(v_a_2619_);
v___x_2621_ = lean_box(0);
if (v_isShared_2608_ == 0)
{
lean_ctor_set_tag(v___x_2607_, 1);
lean_ctor_set(v___x_2607_, 1, v___x_2621_);
lean_ctor_set(v___x_2607_, 0, v_mvarId_2620_);
v___x_2623_ = v___x_2607_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_mvarId_2620_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = l_List_appendTR___redArg(v_snd_2605_, v___x_2623_);
v___x_2625_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2624_, v___y_2589_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2625_;
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2607_);
lean_dec(v_snd_2605_);
v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2618_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2618_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_a_2613_);
lean_dec(v_fvarId_2611_);
lean_del_object(v___x_2607_);
lean_dec(v_snd_2605_);
lean_dec(v_fst_2604_);
v_a_2635_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2614_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2614_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_fvarId_2611_);
lean_del_object(v___x_2607_);
lean_dec(v_snd_2605_);
lean_dec(v_fst_2604_);
v_a_2643_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2612_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2612_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec_ref(v___x_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_snd_2605_);
lean_dec(v_fst_2604_);
v___x_2651_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1, &l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1);
v___x_2652_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2651_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2652_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2602_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2602_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object* v___x_2662_, lean_object* v_stx_2663_, lean_object* v___x_2664_, lean_object* v___x_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_952__boxed_2675_; uint8_t v___x_954__boxed_2676_; lean_object* v_res_2677_; 
v___x_952__boxed_2675_ = lean_unbox(v___x_2662_);
v___x_954__boxed_2676_ = lean_unbox(v___x_2665_);
v_res_2677_ = l_Lean_Elab_Tactic_evalSpecialize___lam__0(v___x_952__boxed_2675_, v_stx_2663_, v___x_2664_, v___x_954__boxed_2676_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v_stx_2663_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object* v_stx_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___y_2700_; lean_object* v___x_2701_; 
v___x_2694_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__0));
v___x_2695_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
lean_inc(v_stx_2684_);
v___x_2696_ = l_Lean_Syntax_isOfKind(v_stx_2684_, v___x_2695_);
v___x_2697_ = 1;
v___x_2698_ = lean_box(v___x_2696_);
v___x_2699_ = lean_box(v___x_2697_);
v___y_2700_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed), 13, 4);
lean_closure_set(v___y_2700_, 0, v___x_2698_);
lean_closure_set(v___y_2700_, 1, v_stx_2684_);
lean_closure_set(v___y_2700_, 2, v___x_2694_);
lean_closure_set(v___y_2700_, 3, v___x_2699_);
v___x_2701_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_2700_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___boxed(lean_object* v_stx_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Elab_Tactic_evalSpecialize(v_stx_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2720_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2721_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2723_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___boxed), 10, 0);
v___x_2724_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2720_, v___x_2721_, v___x_2722_, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6));
v___x_2754_ = l_Lean_addBuiltinDeclarationRanges(v___x_2752_, v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object* v_stx_2758_, uint8_t v_mayPostpone_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; uint8_t v___x_2780_; 
v___x_2780_ = l_Lean_Syntax_isIdent(v_stx_2758_);
if (v___x_2780_ == 0)
{
v___y_2770_ = v_a_2760_;
v___y_2771_ = v_a_2761_;
v___y_2772_ = v_a_2762_;
v___y_2773_ = v_a_2763_;
v___y_2774_ = v_a_2764_;
v___y_2775_ = v_a_2765_;
v___y_2776_ = v_a_2766_;
v___y_2777_ = v_a_2767_;
goto v___jp_2769_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = ((lean_object*)(l_Lean_Elab_Tactic_elabTermForApply___closed__0));
lean_inc(v_stx_2758_);
v___x_2782_ = l_Lean_Elab_Term_resolveId_x3f(v_stx_2758_, v___x_2781_, v___x_2780_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2791_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
if (lean_obj_tag(v_a_2783_) == 1)
{
lean_object* v_val_2787_; lean_object* v___x_2789_; 
lean_dec(v_stx_2758_);
v_val_2787_ = lean_ctor_get(v_a_2783_, 0);
lean_inc(v_val_2787_);
lean_dec_ref_known(v_a_2783_, 1);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v_val_2787_);
v___x_2789_ = v___x_2785_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_val_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
else
{
lean_del_object(v___x_2785_);
lean_dec(v_a_2783_);
v___y_2770_ = v_a_2760_;
v___y_2771_ = v_a_2761_;
v___y_2772_ = v_a_2762_;
v___y_2773_ = v_a_2763_;
v___y_2774_ = v_a_2764_;
v___y_2775_ = v_a_2765_;
v___y_2776_ = v_a_2766_;
v___y_2777_ = v_a_2767_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_stx_2758_);
v_a_2792_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2782_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2782_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
v___jp_2769_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = l_Lean_Elab_Tactic_elabTerm(v_stx_2758_, v___x_2778_, v_mayPostpone_2759_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object* v_stx_2800_, lean_object* v_mayPostpone_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
uint8_t v_mayPostpone_boxed_2811_; lean_object* v_res_2812_; 
v_mayPostpone_boxed_2811_ = lean_unbox(v_mayPostpone_2801_);
v_res_2812_ = l_Lean_Elab_Tactic_elabTermForApply(v_stx_2800_, v_mayPostpone_boxed_2811_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2812_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2));
v___x_2818_ = l_Lean_stringToMessageData(v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object* v___x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2844_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2844_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2844_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
if (lean_obj_tag(v_a_2830_) == 1)
{
lean_object* v_fvarId_2834_; lean_object* v___x_2836_; 
v_fvarId_2834_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_fvarId_2834_);
lean_dec_ref_known(v_a_2830_, 1);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v_fvarId_2834_);
v___x_2836_ = v___x_2832_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_fvarId_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_del_object(v___x_2832_);
v___x_2838_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1);
v___x_2839_ = l_Lean_MessageData_ofExpr(v_a_2830_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2842_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2829_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2829_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(lean_object* v___x_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Elab_Tactic_getFVarId___lam__0(v___x_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* v_id_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_toCold_2874_; lean_object* v_options_2875_; lean_object* v_currRecDepth_2876_; lean_object* v_maxRecDepth_2877_; lean_object* v_ref_2878_; lean_object* v_currNamespace_2879_; lean_object* v_openDecls_2880_; lean_object* v_initHeartbeats_2881_; lean_object* v_maxHeartbeats_2882_; lean_object* v_currMacroScope_2883_; uint8_t v_diag_2884_; uint8_t v_suppressElabErrors_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___f_2889_; lean_object* v_ref_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_toCold_2874_ = lean_ctor_get(v_a_2871_, 0);
v_options_2875_ = lean_ctor_get(v_a_2871_, 1);
v_currRecDepth_2876_ = lean_ctor_get(v_a_2871_, 2);
v_maxRecDepth_2877_ = lean_ctor_get(v_a_2871_, 3);
v_ref_2878_ = lean_ctor_get(v_a_2871_, 4);
v_currNamespace_2879_ = lean_ctor_get(v_a_2871_, 5);
v_openDecls_2880_ = lean_ctor_get(v_a_2871_, 6);
v_initHeartbeats_2881_ = lean_ctor_get(v_a_2871_, 7);
v_maxHeartbeats_2882_ = lean_ctor_get(v_a_2871_, 8);
v_currMacroScope_2883_ = lean_ctor_get(v_a_2871_, 9);
v_diag_2884_ = lean_ctor_get_uint8(v_a_2871_, sizeof(void*)*10);
v_suppressElabErrors_2885_ = lean_ctor_get_uint8(v_a_2871_, sizeof(void*)*10 + 1);
v___x_2886_ = 0;
v___x_2887_ = lean_box(v___x_2886_);
lean_inc(v_id_2864_);
v___x_2888_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_2888_, 0, v_id_2864_);
lean_closure_set(v___x_2888_, 1, v___x_2887_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2889_, 0, v___x_2888_);
v_ref_2890_ = l_Lean_replaceRef(v_id_2864_, v_ref_2878_);
lean_dec(v_id_2864_);
lean_inc(v_currMacroScope_2883_);
lean_inc(v_maxHeartbeats_2882_);
lean_inc(v_initHeartbeats_2881_);
lean_inc(v_openDecls_2880_);
lean_inc(v_currNamespace_2879_);
lean_inc(v_maxRecDepth_2877_);
lean_inc(v_currRecDepth_2876_);
lean_inc_ref(v_options_2875_);
lean_inc_ref(v_toCold_2874_);
v___x_2891_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2891_, 0, v_toCold_2874_);
lean_ctor_set(v___x_2891_, 1, v_options_2875_);
lean_ctor_set(v___x_2891_, 2, v_currRecDepth_2876_);
lean_ctor_set(v___x_2891_, 3, v_maxRecDepth_2877_);
lean_ctor_set(v___x_2891_, 4, v_ref_2890_);
lean_ctor_set(v___x_2891_, 5, v_currNamespace_2879_);
lean_ctor_set(v___x_2891_, 6, v_openDecls_2880_);
lean_ctor_set(v___x_2891_, 7, v_initHeartbeats_2881_);
lean_ctor_set(v___x_2891_, 8, v_maxHeartbeats_2882_);
lean_ctor_set(v___x_2891_, 9, v_currMacroScope_2883_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*10, v_diag_2884_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*10 + 1, v_suppressElabErrors_2885_);
v___x_2892_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2889_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v___x_2891_, v_a_2872_);
lean_dec_ref_known(v___x_2891_, 10);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object* v_id_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Elab_Tactic_getFVarId(v_id_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t v_sz_2904_, size_t v_i_2905_, lean_object* v_bs_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_usize_dec_lt(v_i_2905_, v_sz_2904_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_bs_2906_);
return v___x_2917_;
}
else
{
lean_object* v_v_2918_; lean_object* v___x_2919_; 
v_v_2918_ = lean_array_uget_borrowed(v_bs_2906_, v_i_2905_);
lean_inc(v_v_2918_);
v___x_2919_ = l_Lean_Elab_Tactic_getFVarId(v_v_2918_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v_bs_x27_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = lean_unsigned_to_nat(0u);
v_bs_x27_2922_ = lean_array_uset(v_bs_2906_, v_i_2905_, v___x_2921_);
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_add(v_i_2905_, v___x_2923_);
v___x_2925_ = lean_array_uset(v_bs_x27_2922_, v_i_2905_, v_a_2920_);
v_i_2905_ = v___x_2924_;
v_bs_2906_ = v___x_2925_;
goto _start;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_bs_2906_);
v_a_2927_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2919_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2919_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_bs_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_sz_boxed_2947_; size_t v_i_boxed_2948_; lean_object* v_res_2949_; 
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2948_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(v_sz_boxed_2947_, v_i_boxed_2948_, v_bs_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* v_ids_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
size_t v_sz_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_sz_2962_ = lean_array_size(v_ids_2952_);
v___x_2963_ = lean_box_usize(v_sz_2962_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1));
v___x_2965_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed), 12, 3);
lean_closure_set(v___x_2965_, 0, v___x_2963_);
lean_closure_set(v___x_2965_, 1, v___x_2964_);
lean_closure_set(v___x_2965_, 2, v_ids_2952_);
v___x_2966_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2965_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object* v_ids_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_Elab_Tactic_getFVarIds(v_ids_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object* v_e_2978_, uint8_t v___x_2979_, lean_object* v_tac_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_val_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Elab_Tactic_elabTermForApply(v_e_2978_, v___x_2979_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; lean_object* v_a_3025_; uint8_t v___x_3026_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_3023_, v___y_2986_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = l_Lean_Expr_isMVar(v_a_3025_);
if (v___x_3026_ == 0)
{
v_val_2991_ = v_a_3025_;
v___y_2992_ = v___y_2982_;
v___y_2993_ = v___y_2983_;
v___y_2994_ = v___y_2984_;
v___y_2995_ = v___y_2985_;
v___y_2996_ = v___y_2986_;
v___y_2997_ = v___y_2987_;
v___y_2998_ = v___y_2988_;
goto v___jp_2990_;
}
else
{
uint8_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = 0;
v___x_3028_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3027_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3029_; lean_object* v_a_3030_; 
lean_dec_ref_known(v___x_3028_, 1);
v___x_3029_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_3025_, v___y_2986_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v_val_2991_ = v_a_3030_;
v___y_2992_ = v___y_2982_;
v___y_2993_ = v___y_2983_;
v___y_2994_ = v___y_2984_;
v___y_2995_ = v___y_2985_;
v___y_2996_ = v___y_2986_;
v___y_2997_ = v___y_2987_;
v___y_2998_ = v___y_2988_;
goto v___jp_2990_;
}
else
{
lean_dec(v_a_3025_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec_ref(v_tac_2980_);
return v___x_3028_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec_ref(v_tac_2980_);
v_a_3031_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3022_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3022_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
v___jp_2990_:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2992_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_2997_);
lean_inc(v___y_2996_);
lean_inc_ref(v___y_2995_);
v___x_3001_ = lean_apply_7(v_tac_2980_, v_a_3000_, v_val_2991_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, lean_box(0));
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = 0;
v___x_3004_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3003_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; 
lean_dec_ref_known(v___x_3004_, 1);
v___x_3005_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3002_, v___y_2992_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v___x_3005_;
}
else
{
lean_dec(v_a_3002_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v___x_3004_;
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
v_a_3006_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3001_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3001_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v_val_2991_);
lean_dec_ref(v_tac_2980_);
v_a_3014_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2999_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2999_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object* v_e_3039_, lean_object* v___x_3040_, lean_object* v_tac_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
uint8_t v___x_921__boxed_3051_; lean_object* v_res_3052_; 
v___x_921__boxed_3051_ = lean_unbox(v___x_3040_);
v_res_3052_ = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(v_e_3039_, v___x_921__boxed_3051_, v_tac_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* v_tac_3053_, lean_object* v_e_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; 
v___x_3064_ = 1;
v___x_3065_ = lean_box(v___x_3064_);
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3066_, 0, v_e_3054_);
lean_closure_set(v___f_3066_, 1, v___x_3065_);
lean_closure_set(v___f_3066_, 2, v_tac_3053_);
v___x_3067_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3066_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object* v_tac_3068_, lean_object* v_e_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v_tac_3068_, v_e_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t v___x_3080_, lean_object* v_g_3081_, lean_object* v_e_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
uint8_t v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3088_ = 0;
v___x_3089_ = 0;
v___x_3090_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3090_, 0, v___x_3088_);
lean_ctor_set_uint8(v___x_3090_, 1, v___x_3080_);
lean_ctor_set_uint8(v___x_3090_, 2, v___x_3089_);
lean_ctor_set_uint8(v___x_3090_, 3, v___x_3080_);
v___x_3091_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
lean_inc_ref(v_e_3082_);
v___x_3092_ = l_Lean_MessageData_ofExpr(v_e_3082_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3091_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
v___x_3096_ = l_Lean_MVarId_apply(v_g_3081_, v_e_3082_, v___x_3090_, v___x_3095_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object* v___x_3097_, lean_object* v_g_3098_, lean_object* v_e_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
uint8_t v___x_159__boxed_3105_; lean_object* v_res_3106_; 
v___x_159__boxed_3105_ = lean_unbox(v___x_3097_);
v_res_3106_ = l_Lean_Elab_Tactic_evalApply___lam__0(v___x_159__boxed_3105_, v_g_3098_, v_e_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* v_stx_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
lean_inc(v_stx_3113_);
v___x_3124_ = l_Lean_Syntax_isOfKind(v_stx_3113_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_dec(v_stx_3113_);
v___x_3125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; lean_object* v___f_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3126_ = lean_box(v___x_3124_);
v___f_3127_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3127_, 0, v___x_3126_);
v___x_3128_ = lean_unsigned_to_nat(1u);
v___x_3129_ = l_Lean_Syntax_getArg(v_stx_3113_, v___x_3128_);
lean_dec(v_stx_3113_);
v___x_3130_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v___f_3127_, v___x_3129_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
return v___x_3130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object* v_stx_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Elab_Tactic_evalApply(v_stx_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3150_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3152_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___boxed), 10, 0);
v___x_3153_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3149_, v___x_3150_, v___x_3151_, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6));
v___x_3184_ = l_Lean_addBuiltinDeclarationRanges(v___x_3182_, v___x_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
return v_res_3186_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_box(0);
v___x_3188_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v___x_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___closed__0);
v___x_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(lean_object* v_00_u03b1_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0(v_00_u03b1_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(lean_object* v_msg_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_ref_3215_; lean_object* v___x_3216_; lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3225_; 
v_ref_3215_ = lean_ctor_get(v___y_3212_, 4);
v___x_3216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3225_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3225_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_inc(v_ref_3215_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_ref_3215_);
lean_ctor_set(v___x_3221_, 1, v_a_3217_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 1);
lean_ctor_set(v___x_3219_, 0, v___x_3221_);
v___x_3223_ = v___x_3219_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v_msg_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
return v_res_3232_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__1));
v___x_3236_ = l_Lean_stringToMessageData(v___x_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(lean_object* v___x_3237_, lean_object* v_ctor_3238_, lean_object* v_args_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__0));
v___x_3266_ = lean_string_dec_eq(v_ctor_3238_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__0___redArg();
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3268_ = lean_array_get_size(v_args_3239_);
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_nat_dec_eq(v___x_3268_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v___x_3271_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___closed__2);
v___x_3272_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v___x_3271_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
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
else
{
goto v___jp_3245_;
}
}
v___jp_3245_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = lean_unsigned_to_nat(0u);
v___x_3247_ = lean_array_get_borrowed(v___x_3237_, v_args_3239_, v___x_3246_);
lean_inc(v___x_3247_);
v___x_3248_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_3247_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_a_3257_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3248_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3248_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed(lean_object* v___x_3281_, lean_object* v_ctor_3282_, lean_object* v_args_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0(v___x_3281_, v_ctor_3282_, v_args_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec_ref(v_args_3283_);
lean_dec_ref(v_ctor_3282_);
lean_dec_ref(v___x_3281_);
return v_res_3289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___f_3291_; 
v___x_3290_ = l_Lean_instInhabitedExpr;
v___f_3291_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3291_, 0, v___x_3290_);
return v___f_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v___f_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___f_3304_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__0);
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3306_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_3305_, v___f_3304_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___boxed(lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(lean_object* v_00_u03b1_3314_, lean_object* v_msg_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___redArg(v_msg_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_3322_, lean_object* v_msg_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr_spec__1(v_00_u03b1_3322_, v_msg_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3329_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_box(0);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3333_ = l_Lean_Expr_const___override(v___x_3332_, v___x_3331_);
return v___x_3333_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2);
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__0));
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___x_3336_);
return v___x_3338_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig(void){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__3);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = l_Lean_Elab_abortTermExceptionId;
v___x_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v___x_3340_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg(){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(lean_object* v_e_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_3351_; 
v___x_3351_ = l_Lean_Expr_hasMVar(v_e_3348_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_e_3348_);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; lean_object* v_mctx_3354_; lean_object* v___x_3355_; lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3358_; lean_object* v_cache_3359_; lean_object* v_zetaDeltaFVarIds_3360_; lean_object* v_postponed_3361_; lean_object* v_diag_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3371_; 
v___x_3353_ = lean_st_ref_get(v___y_3349_);
v_mctx_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_mctx_3354_);
lean_dec(v___x_3353_);
v___x_3355_ = l_Lean_instantiateMVarsCore(v_mctx_3354_, v_e_3348_);
v_fst_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_fst_3356_);
v_snd_3357_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_snd_3357_);
lean_dec_ref(v___x_3355_);
v___x_3358_ = lean_st_ref_take(v___y_3349_);
v_cache_3359_ = lean_ctor_get(v___x_3358_, 1);
v_zetaDeltaFVarIds_3360_ = lean_ctor_get(v___x_3358_, 2);
v_postponed_3361_ = lean_ctor_get(v___x_3358_, 3);
v_diag_3362_ = lean_ctor_get(v___x_3358_, 4);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v___x_3358_, 0);
lean_dec(v_unused_3372_);
v___x_3364_ = v___x_3358_;
v_isShared_3365_ = v_isSharedCheck_3371_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_diag_3362_);
lean_inc(v_postponed_3361_);
lean_inc(v_zetaDeltaFVarIds_3360_);
lean_inc(v_cache_3359_);
lean_dec(v___x_3358_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3371_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_snd_3357_);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_snd_3357_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_cache_3359_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_zetaDeltaFVarIds_3360_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_postponed_3361_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_diag_3362_);
v___x_3367_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = lean_st_ref_put(v___y_3349_, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_fst_3356_);
return v___x_3369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v_e_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3373_, v___y_3374_);
lean_dec(v___y_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(lean_object* v_opts_3377_, lean_object* v_opt_3378_){
_start:
{
lean_object* v_name_3379_; lean_object* v_defValue_3380_; lean_object* v_map_3381_; lean_object* v___x_3382_; 
v_name_3379_ = lean_ctor_get(v_opt_3378_, 0);
v_defValue_3380_ = lean_ctor_get(v_opt_3378_, 1);
v_map_3381_ = lean_ctor_get(v_opts_3377_, 0);
v___x_3382_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3381_, v_name_3379_);
if (lean_obj_tag(v___x_3382_) == 0)
{
uint8_t v___x_3383_; 
v___x_3383_ = lean_unbox(v_defValue_3380_);
return v___x_3383_;
}
else
{
lean_object* v_val_3384_; 
v_val_3384_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_val_3384_);
lean_dec_ref_known(v___x_3382_, 1);
if (lean_obj_tag(v_val_3384_) == 1)
{
uint8_t v_v_3385_; 
v_v_3385_ = lean_ctor_get_uint8(v_val_3384_, 0);
lean_dec_ref_known(v_val_3384_, 0);
return v_v_3385_;
}
else
{
uint8_t v___x_3386_; 
lean_dec(v_val_3384_);
v___x_3386_ = lean_unbox(v_defValue_3380_);
return v___x_3386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_3387_, lean_object* v_opt_3388_){
_start:
{
uint8_t v_res_3389_; lean_object* v_r_3390_; 
v_res_3389_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_3387_, v_opt_3388_);
lean_dec_ref(v_opt_3388_);
lean_dec_ref(v_opts_3387_);
v_r_3390_ = lean_box(v_res_3389_);
return v_r_3390_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_box(1);
v___x_3392_ = l_Lean_MessageData_ofFormat(v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2));
v___x_3397_ = l_Lean_MessageData_ofFormat(v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(lean_object* v_x_3398_, lean_object* v_x_3399_){
_start:
{
if (lean_obj_tag(v_x_3399_) == 0)
{
return v_x_3398_;
}
else
{
lean_object* v_head_3400_; lean_object* v_tail_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3423_; 
v_head_3400_ = lean_ctor_get(v_x_3399_, 0);
v_tail_3401_ = lean_ctor_get(v_x_3399_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_x_3399_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3403_ = v_x_3399_;
v_isShared_3404_ = v_isSharedCheck_3423_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_tail_3401_);
lean_inc(v_head_3400_);
lean_dec(v_x_3399_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3423_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_before_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3421_; 
v_before_3405_ = lean_ctor_get(v_head_3400_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_head_3400_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v_head_3400_, 1);
lean_dec(v_unused_3422_);
v___x_3407_ = v_head_3400_;
v_isShared_3408_ = v_isSharedCheck_3421_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_before_3405_);
lean_dec(v_head_3400_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3421_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set_tag(v___x_3407_, 7);
lean_ctor_set(v___x_3407_, 1, v___x_3409_);
lean_ctor_set(v___x_3407_, 0, v_x_3398_);
v___x_3411_ = v___x_3407_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_x_3398_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3412_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 7);
lean_ctor_set(v___x_3403_, 1, v___x_3412_);
lean_ctor_set(v___x_3403_, 0, v___x_3411_);
v___x_3414_ = v___x_3403_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = l_Lean_MessageData_ofSyntax(v_before_3405_);
v___x_3416_ = l_Lean_indentD(v___x_3415_);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3414_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v_x_3398_ = v___x_3417_;
v_x_3399_ = v_tail_3401_;
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
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_3428_ = l_Lean_MessageData_ofFormat(v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_3429_, lean_object* v_macroStack_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_options_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_options_3433_ = lean_ctor_get(v___y_3431_, 1);
v___x_3434_ = l_Lean_Elab_pp_macroStack;
v___x_3435_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; 
lean_dec(v_macroStack_3430_);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v_msgData_3429_);
return v___x_3436_;
}
else
{
if (lean_obj_tag(v_macroStack_3430_) == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_msgData_3429_);
return v___x_3437_;
}
else
{
lean_object* v_head_3438_; lean_object* v_after_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3454_; 
v_head_3438_ = lean_ctor_get(v_macroStack_3430_, 0);
lean_inc(v_head_3438_);
v_after_3439_ = lean_ctor_get(v_head_3438_, 1);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_head_3438_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v_head_3438_, 0);
lean_dec(v_unused_3455_);
v___x_3441_ = v_head_3438_;
v_isShared_3442_ = v_isSharedCheck_3454_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_after_3439_);
lean_dec(v_head_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3454_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 7);
lean_ctor_set(v___x_3441_, 1, v___x_3443_);
lean_ctor_set(v___x_3441_, 0, v_msgData_3429_);
v___x_3445_ = v___x_3441_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_msgData_3429_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v_msgData_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3446_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l_Lean_MessageData_ofSyntax(v_after_3439_);
v___x_3449_ = l_Lean_indentD(v___x_3448_);
v_msgData_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3450_, 0, v___x_3447_);
lean_ctor_set(v_msgData_3450_, 1, v___x_3449_);
v___x_3451_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_3450_, v_macroStack_3430_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3456_, lean_object* v_macroStack_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3456_, v_macroStack_3457_, v___y_3458_);
lean_dec_ref(v___y_3458_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(lean_object* v_msg_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_ref_3469_; lean_object* v___x_3470_; lean_object* v_a_3471_; lean_object* v_macroStack_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3483_; 
v_ref_3469_ = lean_ctor_get(v___y_3466_, 4);
v___x_3470_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_3461_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3470_);
v_macroStack_3472_ = lean_ctor_get(v___y_3462_, 1);
v___x_3473_ = l_Lean_Elab_getBetterRef(v_ref_3469_, v_macroStack_3472_);
lean_inc(v_macroStack_3472_);
v___x_3474_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_3471_, v_macroStack_3472_, v___y_3466_);
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3473_);
lean_ctor_set(v___x_3479_, 1, v_a_3475_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set_tag(v___x_3477_, 1);
lean_ctor_set(v___x_3477_, 0, v___x_3479_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(lean_object* v_msg_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
return v_res_3492_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__0));
v___x_3495_ = l_Lean_stringToMessageData(v___x_3494_);
return v___x_3495_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__1);
v___x_3497_ = l_Lean_MessageData_ofExpr(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__2);
v___x_3499_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__1);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_3502_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__3);
v___x_3503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__5));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__7));
v___x_3509_ = l_Lean_stringToMessageData(v___x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(lean_object* v_stx_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_ty_x3f_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v_toCold_3524_; lean_object* v_options_3525_; lean_object* v_currRecDepth_3526_; lean_object* v_maxRecDepth_3527_; lean_object* v_ref_3528_; lean_object* v_currNamespace_3529_; lean_object* v_openDecls_3530_; lean_object* v_initHeartbeats_3531_; lean_object* v_maxHeartbeats_3532_; lean_object* v_currMacroScope_3533_; uint8_t v_diag_3534_; uint8_t v_suppressElabErrors_3535_; uint8_t v___x_3536_; lean_object* v_ref_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_ty_x3f_3518_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig___closed__2);
v___x_3519_ = 1;
v___x_3520_ = lean_box(0);
v___x_3521_ = lean_box(v___x_3519_);
v___x_3522_ = lean_box(v___x_3519_);
lean_inc(v_stx_3510_);
v___x_3523_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3523_, 0, v_stx_3510_);
lean_closure_set(v___x_3523_, 1, v_ty_x3f_3518_);
lean_closure_set(v___x_3523_, 2, v___x_3521_);
lean_closure_set(v___x_3523_, 3, v___x_3522_);
lean_closure_set(v___x_3523_, 4, v___x_3520_);
v_toCold_3524_ = lean_ctor_get(v_a_3515_, 0);
v_options_3525_ = lean_ctor_get(v_a_3515_, 1);
v_currRecDepth_3526_ = lean_ctor_get(v_a_3515_, 2);
v_maxRecDepth_3527_ = lean_ctor_get(v_a_3515_, 3);
v_ref_3528_ = lean_ctor_get(v_a_3515_, 4);
v_currNamespace_3529_ = lean_ctor_get(v_a_3515_, 5);
v_openDecls_3530_ = lean_ctor_get(v_a_3515_, 6);
v_initHeartbeats_3531_ = lean_ctor_get(v_a_3515_, 7);
v_maxHeartbeats_3532_ = lean_ctor_get(v_a_3515_, 8);
v_currMacroScope_3533_ = lean_ctor_get(v_a_3515_, 9);
v_diag_3534_ = lean_ctor_get_uint8(v_a_3515_, sizeof(void*)*10);
v_suppressElabErrors_3535_ = lean_ctor_get_uint8(v_a_3515_, sizeof(void*)*10 + 1);
v___x_3536_ = 1;
v_ref_3537_ = l_Lean_replaceRef(v_stx_3510_, v_ref_3528_);
lean_dec(v_stx_3510_);
lean_inc(v_currMacroScope_3533_);
lean_inc(v_maxHeartbeats_3532_);
lean_inc(v_initHeartbeats_3531_);
lean_inc(v_openDecls_3530_);
lean_inc(v_currNamespace_3529_);
lean_inc(v_maxRecDepth_3527_);
lean_inc(v_currRecDepth_3526_);
lean_inc_ref(v_options_3525_);
lean_inc_ref(v_toCold_3524_);
v___x_3538_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3538_, 0, v_toCold_3524_);
lean_ctor_set(v___x_3538_, 1, v_options_3525_);
lean_ctor_set(v___x_3538_, 2, v_currRecDepth_3526_);
lean_ctor_set(v___x_3538_, 3, v_maxRecDepth_3527_);
lean_ctor_set(v___x_3538_, 4, v_ref_3537_);
lean_ctor_set(v___x_3538_, 5, v_currNamespace_3529_);
lean_ctor_set(v___x_3538_, 6, v_openDecls_3530_);
lean_ctor_set(v___x_3538_, 7, v_initHeartbeats_3531_);
lean_ctor_set(v___x_3538_, 8, v_maxHeartbeats_3532_);
lean_ctor_set(v___x_3538_, 9, v_currMacroScope_3533_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*10, v_diag_3534_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*10 + 1, v_suppressElabErrors_3535_);
v___x_3539_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3523_, v___x_3536_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v___x_3538_, v_a_3516_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v_a_3542_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; uint8_t v___x_3637_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_3540_, v_a_3514_);
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v___x_3637_ = l_Lean_Expr_hasSorry(v_a_3542_);
if (v___x_3637_ == 0)
{
v___y_3582_ = v_a_3511_;
v___y_3583_ = v_a_3512_;
v___y_3584_ = v_a_3513_;
v___y_3585_ = v_a_3514_;
v___y_3586_ = v___x_3538_;
v___y_3587_ = v_a_3516_;
goto v___jp_3581_;
}
else
{
uint8_t v___x_3638_; 
v___x_3638_ = l_Lean_Expr_hasSyntheticSorry(v_a_3542_);
if (v___x_3638_ == 0)
{
v___y_3619_ = v_a_3511_;
v___y_3620_ = v_a_3512_;
v___y_3621_ = v_a_3513_;
v___y_3622_ = v_a_3514_;
v___y_3623_ = v___x_3538_;
v___y_3624_ = v_a_3516_;
goto v___jp_3618_;
}
else
{
lean_object* v___x_3639_; lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v_a_3542_);
lean_dec_ref_known(v___x_3538_, 10);
v___x_3639_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
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
v___jp_3543_:
{
if (v___y_3553_ == 0)
{
if (lean_obj_tag(v___y_3544_) == 0)
{
lean_dec_ref_known(v___y_3544_, 2);
lean_dec_ref(v___y_3545_);
lean_dec(v_a_3542_);
return v___y_3549_;
}
else
{
lean_object* v_id_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3567_; 
v_id_3554_ = lean_ctor_get(v___y_3544_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___y_3544_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v___y_3544_, 1);
lean_dec(v_unused_3568_);
v___x_3556_ = v___y_3544_;
v_isShared_3557_ = v_isSharedCheck_3567_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_id_3554_);
lean_dec(v___y_3544_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3567_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3548_, v_id_3554_);
lean_dec(v_id_3554_);
if (v___x_3558_ == 0)
{
lean_del_object(v___x_3556_);
lean_dec_ref(v___y_3545_);
lean_dec(v_a_3542_);
return v___y_3549_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_dec_ref(v___y_3549_);
v___x_3559_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__4);
v___x_3560_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__6);
v___x_3561_ = l_Lean_indentExpr(v_a_3542_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set_tag(v___x_3556_, 7);
lean_ctor_set(v___x_3556_, 1, v___x_3561_);
lean_ctor_set(v___x_3556_, 0, v___x_3560_);
v___x_3563_ = v___x_3556_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3559_);
v___x_3565_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3564_, v___y_3550_, v___y_3546_, v___y_3547_, v___y_3551_, v___y_3545_, v___y_3552_);
lean_dec_ref(v___y_3545_);
return v___x_3565_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v_a_3542_);
return v___y_3549_;
}
}
v___jp_3569_:
{
lean_object* v___x_3576_; 
lean_inc(v_a_3542_);
v___x_3576_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr(v_a_3542_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_dec_ref(v___y_3574_);
lean_dec(v_a_3542_);
return v___x_3576_;
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
v___x_3578_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3579_ = l_Lean_Exception_isInterrupt(v_a_3577_);
if (v___x_3579_ == 0)
{
uint8_t v___x_3580_; 
lean_inc(v_a_3577_);
v___x_3580_ = l_Lean_Exception_isRuntime(v_a_3577_);
v___y_3544_ = v_a_3577_;
v___y_3545_ = v___y_3574_;
v___y_3546_ = v___y_3571_;
v___y_3547_ = v___y_3572_;
v___y_3548_ = v___x_3578_;
v___y_3549_ = v___x_3576_;
v___y_3550_ = v___y_3570_;
v___y_3551_ = v___y_3573_;
v___y_3552_ = v___y_3575_;
v___y_3553_ = v___x_3580_;
goto v___jp_3543_;
}
else
{
v___y_3544_ = v_a_3577_;
v___y_3545_ = v___y_3574_;
v___y_3546_ = v___y_3571_;
v___y_3547_ = v___y_3572_;
v___y_3548_ = v___x_3578_;
v___y_3549_ = v___x_3576_;
v___y_3550_ = v___y_3570_;
v___y_3551_ = v___y_3573_;
v___y_3552_ = v___y_3575_;
v___y_3553_ = v___x_3579_;
goto v___jp_3543_;
}
}
}
v___jp_3581_:
{
lean_object* v___x_3588_; 
lean_inc(v_a_3542_);
v___x_3588_ = l_Lean_Meta_getMVars(v_a_3542_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3589_, v___x_3520_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v_a_3589_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; uint8_t v___x_3592_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3592_ = lean_unbox(v_a_3591_);
lean_dec(v_a_3591_);
if (v___x_3592_ == 0)
{
v___y_3570_ = v___y_3582_;
v___y_3571_ = v___y_3583_;
v___y_3572_ = v___y_3584_;
v___y_3573_ = v___y_3585_;
v___y_3574_ = v___y_3586_;
v___y_3575_ = v___y_3587_;
goto v___jp_3569_;
}
else
{
lean_object* v___x_3593_; lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v___y_3586_);
lean_dec(v_a_3542_);
v___x_3593_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3593_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3593_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec_ref(v___y_3586_);
lean_dec(v_a_3542_);
v_a_3602_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3590_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3590_);
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
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref(v___y_3586_);
lean_dec(v_a_3542_);
v_a_3610_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3588_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3588_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
v___jp_3618_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v___x_3625_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___closed__8);
v___x_3626_ = l_Lean_indentExpr(v_a_3542_);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3627_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec_ref(v___y_3623_);
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref_known(v___x_3538_, 10);
v_a_3648_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3539_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3539_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(v_stx_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(uint8_t v_config_3675_, lean_object* v_item_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_item_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3695_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3676_, v___x_3694_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3695_) == 0)
{
uint8_t v___x_3696_; 
lean_dec_ref_known(v___x_3695_, 1);
v___x_3696_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3676_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3697_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3676_);
lean_inc_ref(v_item_3676_);
v___x_3698_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3676_);
v___x_3699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__1));
v___x_3700_ = lean_string_dec_eq(v___x_3697_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__2));
v___x_3702_ = lean_string_dec_eq(v___x_3697_, v___x_3701_);
lean_dec_ref(v___x_3697_);
if (v___x_3702_ == 0)
{
lean_dec_ref(v_item_3676_);
v_item_3685_ = v___x_3698_;
v___y_3686_ = v___y_3677_;
v___y_3687_ = v___y_3678_;
v___y_3688_ = v___y_3679_;
v___y_3689_ = v___y_3680_;
v___y_3690_ = v___y_3681_;
v___y_3691_ = v___y_3682_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__3));
v___x_3704_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3676_, v___x_3703_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3704_) == 0)
{
uint8_t v___x_3705_; 
lean_dec_ref_known(v___x_3704_, 1);
v___x_3705_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3698_);
if (v___x_3705_ == 0)
{
lean_dec_ref(v_item_3676_);
v_item_3685_ = v___x_3698_;
v___y_3686_ = v___y_3677_;
v___y_3687_ = v___y_3678_;
v___y_3688_ = v___y_3679_;
v___y_3689_ = v___y_3680_;
v___y_3690_ = v___y_3681_;
v___y_3691_ = v___y_3682_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3706_; 
lean_dec_ref(v___x_3698_);
v___x_3706_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
v_a_3715_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3706_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3706_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v___x_3698_);
lean_dec_ref(v_item_3676_);
v_a_3723_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3704_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3704_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
else
{
uint8_t v___x_3731_; 
lean_dec_ref(v___x_3697_);
v___x_3731_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3698_);
if (v___x_3731_ == 0)
{
lean_dec_ref(v_item_3676_);
v_item_3685_ = v___x_3698_;
v___y_3686_ = v___y_3677_;
v___y_3687_ = v___y_3678_;
v___y_3688_ = v___y_3679_;
v___y_3689_ = v___y_3680_;
v___y_3690_ = v___y_3681_;
v___y_3691_ = v___y_3682_;
goto v___jp_3684_;
}
else
{
lean_object* v_value_3732_; lean_object* v___x_3733_; 
lean_dec_ref(v___x_3698_);
v_value_3732_ = lean_ctor_get(v_item_3676_, 2);
lean_inc(v_value_3732_);
lean_dec_ref(v_item_3676_);
v___x_3733_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0(v_value_3732_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
return v___x_3733_;
}
}
}
else
{
v_item_3685_ = v_item_3676_;
v___y_3686_ = v___y_3677_;
v___y_3687_ = v___y_3678_;
v___y_3688_ = v___y_3679_;
v___y_3689_ = v___y_3680_;
v___y_3690_ = v___y_3681_;
v___y_3691_ = v___y_3682_;
goto v___jp_3684_;
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v_item_3676_);
v_a_3734_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3695_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3695_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
v___jp_3684_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___closed__0));
v___x_3693_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3685_, v___x_3692_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3742_, lean_object* v_item_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
uint8_t v_config_3644__boxed_3751_; lean_object* v_res_3752_; 
v_config_3644__boxed_3751_ = lean_unbox(v_config_3742_);
v_res_3752_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___lam__0(v_config_3644__boxed_3751_, v_item_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(lean_object* v_e_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3755_, v___y_3759_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_e_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__0(v_e_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(lean_object* v_00_u03b1_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___redArg();
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(lean_object* v_00_u03b1_3791_, lean_object* v_msg_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3801_, lean_object* v_msg_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_3801_, v_msg_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(lean_object* v_msgData_3811_, lean_object* v_macroStack_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3811_, v_macroStack_3812_, v___y_3817_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_3821_, lean_object* v_macroStack_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_3821_, v_macroStack_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3830_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_box(0);
v___x_3832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_instEvalExprConstructorConfig_evalExpr___closed__2));
v___x_3833_ = l_Lean_mkConst(v___x_3832_, v___x_3831_);
return v___x_3833_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__0);
v___x_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(uint8_t v_cfg_3836_, lean_object* v_cfgItem_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = lean_obj_once(&l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___closed__1);
v___x_3846_ = lean_box(v_cfg_3836_);
v___x_3847_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v___x_3846_, v_cfgItem_3837_, v___x_3845_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0___boxed(lean_object* v_cfg_3848_, lean_object* v_cfgItem_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
uint8_t v_cfg_boxed_3857_; lean_object* v_res_3858_; 
v_cfg_boxed_3857_ = lean_unbox(v_cfg_3848_);
v_res_3858_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg___lam__0(v_cfg_boxed_3857_, v_cfgItem_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v_cfgItem_3849_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg(lean_object* v_cfg_3860_, uint8_t v_init_3861_, uint8_t v_logExceptions_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_onErr_3867_; lean_object* v_eval_3868_; 
v_onErr_3867_ = ((lean_object*)(l_Lean_Elab_Tactic_elabConstructorConfig___redArg___closed__0));
v_eval_3868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem___closed__0));
if (v_logExceptions_3862_ == 0)
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_box(v_init_3861_);
v___x_3870_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3868_, v___x_3869_, v_cfg_3860_, v_onErr_3867_, v_logExceptions_3862_, v_a_3864_, v_a_3865_);
return v___x_3870_;
}
else
{
uint8_t v_recover_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_recover_3871_ = lean_ctor_get_uint8(v_a_3863_, sizeof(void*)*1);
v___x_3872_ = lean_box(v_init_3861_);
v___x_3873_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3868_, v___x_3872_, v_cfg_3860_, v_onErr_3867_, v_recover_3871_, v_a_3864_, v_a_3865_);
return v___x_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___redArg___boxed(lean_object* v_cfg_3874_, lean_object* v_init_3875_, lean_object* v_logExceptions_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
uint8_t v_init_boxed_3881_; uint8_t v_logExceptions_boxed_3882_; lean_object* v_res_3883_; 
v_init_boxed_3881_ = lean_unbox(v_init_3875_);
v_logExceptions_boxed_3882_ = lean_unbox(v_logExceptions_3876_);
v_res_3883_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v_cfg_3874_, v_init_boxed_3881_, v_logExceptions_boxed_3882_, v_a_3877_, v_a_3878_, v_a_3879_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec_ref(v_a_3877_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig(lean_object* v_cfg_3884_, uint8_t v_init_3885_, uint8_t v_logExceptions_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v_cfg_3884_, v_init_3885_, v_logExceptions_3886_, v_a_3887_, v_a_3893_, v_a_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabConstructorConfig___boxed(lean_object* v_cfg_3897_, lean_object* v_init_3898_, lean_object* v_logExceptions_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
uint8_t v_init_boxed_3909_; uint8_t v_logExceptions_boxed_3910_; lean_object* v_res_3911_; 
v_init_boxed_3909_ = lean_unbox(v_init_3898_);
v_logExceptions_boxed_3910_ = lean_unbox(v_logExceptions_3899_);
v_res_3911_ = l_Lean_Elab_Tactic_elabConstructorConfig(v_cfg_3897_, v_init_boxed_3909_, v_logExceptions_boxed_3910_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
if (lean_obj_tag(v_a_3912_) == 0)
{
lean_object* v___x_3914_; 
v___x_3914_ = l_List_reverse___redArg(v_a_3913_);
return v___x_3914_;
}
else
{
lean_object* v_head_3915_; lean_object* v_tail_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3929_; 
v_head_3915_ = lean_ctor_get(v_a_3912_, 0);
v_tail_3916_ = lean_ctor_get(v_a_3912_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_a_3912_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3918_ = v_a_3912_;
v_isShared_3919_ = v_isSharedCheck_3929_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_tail_3916_);
lean_inc(v_head_3915_);
lean_dec(v_a_3912_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3929_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
uint8_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3920_ = 0;
v___x_3921_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_3922_ = l_Lean_MessageData_ofConstName(v_head_3915_, v___x_3920_);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v___x_3921_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v_a_3913_);
lean_ctor_set(v___x_3918_, 0, v___x_3924_);
v___x_3926_ = v___x_3918_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_a_3913_);
v___x_3926_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
v_a_3912_ = v_tail_3916_;
v_a_3913_ = v___x_3926_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3935_, uint8_t v___y_3936_, lean_object* v_x_3937_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 1)
{
lean_object* v_pre_3938_; 
v_pre_3938_ = lean_ctor_get(v_x_3937_, 0);
switch(lean_obj_tag(v_pre_3938_))
{
case 1:
{
lean_object* v_pre_3939_; 
v_pre_3939_ = lean_ctor_get(v_pre_3938_, 0);
switch(lean_obj_tag(v_pre_3939_))
{
case 0:
{
lean_object* v_str_3940_; lean_object* v_str_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v_str_3940_ = lean_ctor_get(v_x_3937_, 1);
v_str_3941_ = lean_ctor_get(v_pre_3938_, 1);
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1));
v___x_3943_ = lean_string_dec_eq(v_str_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__2));
v___x_3945_ = lean_string_dec_eq(v_str_3941_, v___x_3944_);
if (v___x_3945_ == 0)
{
return v___x_3945_;
}
else
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__0));
v___x_3947_ = lean_string_dec_eq(v_str_3940_, v___x_3946_);
if (v___x_3947_ == 0)
{
return v___x_3947_;
}
else
{
return v_suppressElabErrors_3935_;
}
}
}
else
{
lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3948_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__1));
v___x_3949_ = lean_string_dec_eq(v_str_3940_, v___x_3948_);
if (v___x_3949_ == 0)
{
return v___x_3949_;
}
else
{
return v_suppressElabErrors_3935_;
}
}
}
case 1:
{
lean_object* v_pre_3950_; 
v_pre_3950_ = lean_ctor_get(v_pre_3939_, 0);
if (lean_obj_tag(v_pre_3950_) == 0)
{
lean_object* v_str_3951_; lean_object* v_str_3952_; lean_object* v_str_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v_str_3951_ = lean_ctor_get(v_x_3937_, 1);
v_str_3952_ = lean_ctor_get(v_pre_3938_, 1);
v_str_3953_ = lean_ctor_get(v_pre_3939_, 1);
v___x_3954_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__2));
v___x_3955_ = lean_string_dec_eq(v_str_3953_, v___x_3954_);
if (v___x_3955_ == 0)
{
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__3));
v___x_3957_ = lean_string_dec_eq(v_str_3952_, v___x_3956_);
if (v___x_3957_ == 0)
{
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___closed__4));
v___x_3959_ = lean_string_dec_eq(v_str_3951_, v___x_3958_);
if (v___x_3959_ == 0)
{
return v___x_3959_;
}
else
{
return v_suppressElabErrors_3935_;
}
}
}
}
else
{
return v___y_3936_;
}
}
default: 
{
return v___y_3936_;
}
}
}
case 0:
{
lean_object* v_str_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_str_3960_ = lean_ctor_get(v_x_3937_, 1);
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0));
v___x_3962_ = lean_string_dec_eq(v_str_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
return v___x_3962_;
}
else
{
return v_suppressElabErrors_3935_;
}
}
default: 
{
return v___y_3936_;
}
}
}
else
{
return v___y_3936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3963_, lean_object* v___y_3964_, lean_object* v_x_3965_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3966_; uint8_t v___y_5648__boxed_3967_; uint8_t v_res_3968_; lean_object* v_r_3969_; 
v_suppressElabErrors_boxed_3966_ = lean_unbox(v_suppressElabErrors_3963_);
v___y_5648__boxed_3967_ = lean_unbox(v___y_3964_);
v_res_3968_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3966_, v___y_5648__boxed_3967_, v_x_3965_);
lean_dec(v_x_3965_);
v_r_3969_ = lean_box(v_res_3968_);
return v_r_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_3971_, lean_object* v_msgData_3972_, uint8_t v_severity_3973_, uint8_t v_isSilent_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
uint8_t v___y_3981_; uint8_t v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_4017_; uint8_t v___y_4018_; uint8_t v___y_4019_; uint8_t v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4043_; uint8_t v___y_4044_; uint8_t v___y_4045_; uint8_t v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4053_; uint8_t v___y_4054_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; uint8_t v___y_4058_; uint8_t v___x_4063_; uint8_t v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; uint8_t v___y_4069_; uint8_t v___y_4070_; uint8_t v___y_4072_; uint8_t v___x_4086_; 
v___x_4063_ = 2;
v___x_4086_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3973_, v___x_4063_);
if (v___x_4086_ == 0)
{
v___y_4072_ = v___x_4086_;
goto v___jp_4071_;
}
else
{
uint8_t v___x_4087_; 
lean_inc_ref(v_msgData_3972_);
v___x_4087_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3972_);
v___y_4072_ = v___x_4087_;
goto v___jp_4071_;
}
v___jp_3980_:
{
lean_object* v___x_3990_; lean_object* v_currNamespace_3991_; lean_object* v_openDecls_3992_; lean_object* v_env_3993_; lean_object* v_nextMacroScope_3994_; lean_object* v_ngen_3995_; lean_object* v_auxDeclNGen_3996_; lean_object* v_traceState_3997_; lean_object* v_cache_3998_; lean_object* v_messages_3999_; lean_object* v_infoState_4000_; lean_object* v_snapshotTasks_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4015_; 
v___x_3990_ = lean_st_ref_take(v___y_3989_);
v_currNamespace_3991_ = lean_ctor_get(v___y_3988_, 5);
v_openDecls_3992_ = lean_ctor_get(v___y_3988_, 6);
v_env_3993_ = lean_ctor_get(v___x_3990_, 0);
v_nextMacroScope_3994_ = lean_ctor_get(v___x_3990_, 1);
v_ngen_3995_ = lean_ctor_get(v___x_3990_, 2);
v_auxDeclNGen_3996_ = lean_ctor_get(v___x_3990_, 3);
v_traceState_3997_ = lean_ctor_get(v___x_3990_, 4);
v_cache_3998_ = lean_ctor_get(v___x_3990_, 5);
v_messages_3999_ = lean_ctor_get(v___x_3990_, 6);
v_infoState_4000_ = lean_ctor_get(v___x_3990_, 7);
v_snapshotTasks_4001_ = lean_ctor_get(v___x_3990_, 8);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4003_ = v___x_3990_;
v_isShared_4004_ = v_isSharedCheck_4015_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_snapshotTasks_4001_);
lean_inc(v_infoState_4000_);
lean_inc(v_messages_3999_);
lean_inc(v_cache_3998_);
lean_inc(v_traceState_3997_);
lean_inc(v_auxDeclNGen_3996_);
lean_inc(v_ngen_3995_);
lean_inc(v_nextMacroScope_3994_);
lean_inc(v_env_3993_);
lean_dec(v___x_3990_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4015_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4010_; 
lean_inc(v_openDecls_3992_);
lean_inc(v_currNamespace_3991_);
v___x_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4005_, 0, v_currNamespace_3991_);
lean_ctor_set(v___x_4005_, 1, v_openDecls_3992_);
v___x_4006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v___y_3984_);
lean_inc_ref(v___y_3983_);
lean_inc_ref(v___y_3987_);
v___x_4007_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4007_, 0, v___y_3987_);
lean_ctor_set(v___x_4007_, 1, v___y_3985_);
lean_ctor_set(v___x_4007_, 2, v___y_3986_);
lean_ctor_set(v___x_4007_, 3, v___y_3983_);
lean_ctor_set(v___x_4007_, 4, v___x_4006_);
lean_ctor_set_uint8(v___x_4007_, sizeof(void*)*5, v___y_3981_);
lean_ctor_set_uint8(v___x_4007_, sizeof(void*)*5 + 1, v___y_3982_);
lean_ctor_set_uint8(v___x_4007_, sizeof(void*)*5 + 2, v_isSilent_3974_);
v___x_4008_ = l_Lean_MessageLog_add(v___x_4007_, v_messages_3999_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 6, v___x_4008_);
v___x_4010_ = v___x_4003_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_env_3993_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_nextMacroScope_3994_);
lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_ngen_3995_);
lean_ctor_set(v_reuseFailAlloc_4014_, 3, v_auxDeclNGen_3996_);
lean_ctor_set(v_reuseFailAlloc_4014_, 4, v_traceState_3997_);
lean_ctor_set(v_reuseFailAlloc_4014_, 5, v_cache_3998_);
lean_ctor_set(v_reuseFailAlloc_4014_, 6, v___x_4008_);
lean_ctor_set(v_reuseFailAlloc_4014_, 7, v_infoState_4000_);
lean_ctor_set(v_reuseFailAlloc_4014_, 8, v_snapshotTasks_4001_);
v___x_4010_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4011_ = lean_st_ref_put(v___y_3989_, v___x_4010_);
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
}
v___jp_4016_:
{
lean_object* v_fileName_4024_; lean_object* v_fileMap_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4041_; 
v_fileName_4024_ = lean_ctor_get(v___y_4021_, 0);
v_fileMap_4025_ = lean_ctor_get(v___y_4021_, 1);
v___x_4026_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3972_);
v___x_4027_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v___x_4026_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4041_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4041_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_inc_ref_n(v_fileMap_4025_, 2);
v___x_4032_ = l_Lean_FileMap_toPosition(v_fileMap_4025_, v___y_4022_);
lean_dec(v___y_4022_);
v___x_4033_ = l_Lean_FileMap_toPosition(v_fileMap_4025_, v___y_4023_);
lean_dec(v___y_4023_);
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
v___x_4035_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___closed__0));
if (v___y_4018_ == 0)
{
lean_del_object(v___x_4030_);
lean_dec_ref(v___y_4017_);
v___y_3981_ = v___y_4019_;
v___y_3982_ = v___y_4020_;
v___y_3983_ = v___x_4035_;
v___y_3984_ = v_a_4028_;
v___y_3985_ = v___x_4032_;
v___y_3986_ = v___x_4034_;
v___y_3987_ = v_fileName_4024_;
v___y_3988_ = v___y_3977_;
v___y_3989_ = v___y_3978_;
goto v___jp_3980_;
}
else
{
uint8_t v___x_4036_; 
lean_inc(v_a_4028_);
v___x_4036_ = l_Lean_MessageData_hasTag(v___y_4017_, v_a_4028_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
lean_dec_ref_known(v___x_4034_, 1);
lean_dec_ref(v___x_4032_);
lean_dec(v_a_4028_);
v___x_4037_ = lean_box(0);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v___x_4037_);
v___x_4039_ = v___x_4030_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
else
{
lean_del_object(v___x_4030_);
v___y_3981_ = v___y_4019_;
v___y_3982_ = v___y_4020_;
v___y_3983_ = v___x_4035_;
v___y_3984_ = v_a_4028_;
v___y_3985_ = v___x_4032_;
v___y_3986_ = v___x_4034_;
v___y_3987_ = v_fileName_4024_;
v___y_3988_ = v___y_3977_;
v___y_3989_ = v___y_3978_;
goto v___jp_3980_;
}
}
}
}
v___jp_4042_:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_Syntax_getTailPos_x3f(v___y_4048_, v___y_4045_);
lean_dec(v___y_4048_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_inc(v___y_4049_);
v___y_4017_ = v___y_4043_;
v___y_4018_ = v___y_4044_;
v___y_4019_ = v___y_4045_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___y_4047_;
v___y_4022_ = v___y_4049_;
v___y_4023_ = v___y_4049_;
goto v___jp_4016_;
}
else
{
lean_object* v_val_4051_; 
v_val_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_val_4051_);
lean_dec_ref_known(v___x_4050_, 1);
v___y_4017_ = v___y_4043_;
v___y_4018_ = v___y_4044_;
v___y_4019_ = v___y_4045_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___y_4047_;
v___y_4022_ = v___y_4049_;
v___y_4023_ = v_val_4051_;
goto v___jp_4016_;
}
}
v___jp_4052_:
{
lean_object* v_ref_4059_; lean_object* v___x_4060_; 
v_ref_4059_ = l_Lean_replaceRef(v_ref_3971_, v___y_4056_);
v___x_4060_ = l_Lean_Syntax_getPos_x3f(v_ref_4059_, v___y_4055_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v___x_4061_; 
v___x_4061_ = lean_unsigned_to_nat(0u);
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v_ref_4059_;
v___y_4049_ = v___x_4061_;
goto v___jp_4042_;
}
else
{
lean_object* v_val_4062_; 
v_val_4062_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_val_4062_);
lean_dec_ref_known(v___x_4060_, 1);
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v_ref_4059_;
v___y_4049_ = v_val_4062_;
goto v___jp_4042_;
}
}
v___jp_4064_:
{
if (v___y_4070_ == 0)
{
v___y_4053_ = v___y_4068_;
v___y_4054_ = v___y_4065_;
v___y_4055_ = v___y_4069_;
v___y_4056_ = v___y_4066_;
v___y_4057_ = v___y_4067_;
v___y_4058_ = v_severity_3973_;
goto v___jp_4052_;
}
else
{
v___y_4053_ = v___y_4068_;
v___y_4054_ = v___y_4065_;
v___y_4055_ = v___y_4069_;
v___y_4056_ = v___y_4066_;
v___y_4057_ = v___y_4067_;
v___y_4058_ = v___x_4063_;
goto v___jp_4052_;
}
}
v___jp_4071_:
{
if (v___y_4072_ == 0)
{
lean_object* v_toCold_4073_; lean_object* v_options_4074_; lean_object* v_ref_4075_; uint8_t v_suppressElabErrors_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___f_4079_; uint8_t v___x_4080_; uint8_t v___x_4081_; 
v_toCold_4073_ = lean_ctor_get(v___y_3977_, 0);
v_options_4074_ = lean_ctor_get(v___y_3977_, 1);
v_ref_4075_ = lean_ctor_get(v___y_3977_, 4);
v_suppressElabErrors_4076_ = lean_ctor_get_uint8(v___y_3977_, sizeof(void*)*10 + 1);
v___x_4077_ = lean_box(v_suppressElabErrors_4076_);
v___x_4078_ = lean_box(v___y_4072_);
v___f_4079_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4079_, 0, v___x_4077_);
lean_closure_set(v___f_4079_, 1, v___x_4078_);
v___x_4080_ = 1;
v___x_4081_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3973_, v___x_4080_);
if (v___x_4081_ == 0)
{
v___y_4065_ = v_suppressElabErrors_4076_;
v___y_4066_ = v_ref_4075_;
v___y_4067_ = v_toCold_4073_;
v___y_4068_ = v___f_4079_;
v___y_4069_ = v___y_4072_;
v___y_4070_ = v___x_4081_;
goto v___jp_4064_;
}
else
{
lean_object* v___x_4082_; uint8_t v___x_4083_; 
v___x_4082_ = l_Lean_warningAsError;
v___x_4083_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabConstructorConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_4074_, v___x_4082_);
v___y_4065_ = v_suppressElabErrors_4076_;
v___y_4066_ = v_ref_4075_;
v___y_4067_ = v_toCold_4073_;
v___y_4068_ = v___f_4079_;
v___y_4069_ = v___y_4072_;
v___y_4070_ = v___x_4083_;
goto v___jp_4064_;
}
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec_ref(v_msgData_3972_);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_4088_, lean_object* v_msgData_4089_, lean_object* v_severity_4090_, lean_object* v_isSilent_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
uint8_t v_severity_boxed_4097_; uint8_t v_isSilent_boxed_4098_; lean_object* v_res_4099_; 
v_severity_boxed_4097_ = lean_unbox(v_severity_4090_);
v_isSilent_boxed_4098_ = lean_unbox(v_isSilent_4091_);
v_res_4099_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4088_, v_msgData_4089_, v_severity_boxed_4097_, v_isSilent_boxed_4098_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v_ref_4088_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(lean_object* v_msgData_4100_, uint8_t v_severity_4101_, uint8_t v_isSilent_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_ref_4112_; lean_object* v___x_4113_; 
v_ref_4112_ = lean_ctor_get(v___y_4109_, 4);
v___x_4113_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4112_, v_msgData_4100_, v_severity_4101_, v_isSilent_4102_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1___boxed(lean_object* v_msgData_4114_, lean_object* v_severity_4115_, lean_object* v_isSilent_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v_severity_boxed_4126_; uint8_t v_isSilent_boxed_4127_; lean_object* v_res_4128_; 
v_severity_boxed_4126_ = lean_unbox(v_severity_4115_);
v_isSilent_boxed_4127_ = lean_unbox(v_isSilent_4116_);
v_res_4128_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(v_msgData_4114_, v_severity_boxed_4126_, v_isSilent_boxed_4127_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(lean_object* v_msgData_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
uint8_t v___x_4139_; uint8_t v___x_4140_; lean_object* v___x_4141_; 
v___x_4139_ = 1;
v___x_4140_ = 0;
v___x_4141_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1(v_msgData_4129_, v___x_4139_, v___x_4140_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1___boxed(lean_object* v_msgData_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(v_msgData_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4152_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__0));
v___x_4155_ = l_Lean_stringToMessageData(v___x_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__6));
v___x_4168_ = l_Lean_stringToMessageData(v___x_4167_);
return v___x_4168_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__8));
v___x_4171_ = l_Lean_stringToMessageData(v___x_4170_);
return v___x_4171_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__10));
v___x_4174_ = l_Lean_stringToMessageData(v___x_4173_);
return v___x_4174_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__12));
v___x_4177_ = l_Lean_stringToMessageData(v___x_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(lean_object* v_stx_4180_, lean_object* v___x_4181_, uint8_t v_cfg_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4184_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; uint8_t v___x_4194_; uint8_t v___x_4195_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___x_4218_; uint8_t v___y_4220_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = 1;
v___x_4195_ = 0;
v___x_4218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__2));
if (v_cfg_4182_ == 0)
{
v___y_4220_ = v___x_4194_;
goto v___jp_4219_;
}
else
{
v___y_4220_ = v___x_4195_;
goto v___jp_4219_;
}
v___jp_4196_:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4195_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v___x_4206_; 
lean_dec_ref_known(v___x_4205_, 1);
v___x_4206_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___y_4197_, v___y_4198_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
return v___x_4206_;
}
else
{
lean_dec(v___y_4197_);
return v___x_4205_;
}
}
v___jp_4207_:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_inc_ref(v___y_4211_);
v___x_4212_ = l_Lean_stringToMessageData(v___y_4211_);
v___x_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___y_4208_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__1);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
lean_ctor_set(v___x_4216_, 1, v___y_4209_);
v___x_4217_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1(v___x_4216_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_dec_ref_known(v___x_4217_, 1);
v___y_4197_ = v___y_4210_;
v___y_4198_ = v___y_4184_;
v___y_4199_ = v___y_4185_;
v___y_4200_ = v___y_4186_;
v___y_4201_ = v___y_4187_;
v___y_4202_ = v___y_4188_;
v___y_4203_ = v___y_4189_;
v___y_4204_ = v___y_4190_;
goto v___jp_4196_;
}
else
{
lean_dec(v___y_4210_);
return v___x_4217_;
}
}
v___jp_4219_:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_MVarId_constructorCore(v_a_4193_, v___x_4218_, v___y_4220_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v_fst_4223_; lean_object* v_snd_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4271_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v_fst_4223_ = lean_ctor_get(v_a_4222_, 0);
v_snd_4224_ = lean_ctor_get(v_a_4222_, 1);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_a_4222_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4226_ = v_a_4222_;
v_isShared_4227_ = v_isSharedCheck_4271_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_snd_4224_);
lean_inc(v_fst_4223_);
lean_dec(v_a_4222_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4271_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v___x_4228_ = lean_unsigned_to_nat(1u);
v___x_4229_ = lean_array_get_size(v_snd_4224_);
v___x_4230_ = lean_nat_dec_lt(v___x_4228_, v___x_4229_);
if (v___x_4230_ == 0)
{
lean_del_object(v___x_4226_);
lean_dec(v_snd_4224_);
v___y_4197_ = v_fst_4223_;
v___y_4198_ = v___y_4184_;
v___y_4199_ = v___y_4185_;
v___y_4200_ = v___y_4186_;
v___y_4201_ = v___y_4187_;
v___y_4202_ = v___y_4188_;
v___y_4203_ = v___y_4189_;
v___y_4204_ = v___y_4190_;
goto v___jp_4196_;
}
else
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4231_ = lean_box(0);
v___x_4232_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__5));
v___x_4233_ = lean_unsigned_to_nat(0u);
v___x_4234_ = l_Lean_Syntax_getArg(v_stx_4180_, v___x_4233_);
v___x_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
v___x_4236_ = 4;
v___x_4237_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4237_, 0, v___x_4232_);
lean_ctor_set(v___x_4237_, 1, v___x_4235_);
lean_ctor_set(v___x_4237_, 2, v___x_4231_);
lean_ctor_set_uint8(v___x_4237_, sizeof(void*)*3, v___x_4236_);
v___x_4238_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__7);
v___x_4239_ = lean_mk_empty_array_with_capacity(v___x_4228_);
v___x_4240_ = lean_array_push(v___x_4239_, v___x_4237_);
v___x_4241_ = l_Lean_MessageData_hint(v___x_4238_, v___x_4240_, v___x_4231_, v___x_4231_, v___x_4195_, v___y_4189_, v___y_4190_);
lean_dec_ref(v___x_4240_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4252_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
lean_inc(v_snd_4224_);
v___x_4243_ = lean_array_to_list(v_snd_4224_);
v___x_4244_ = l_List_drop___redArg(v___x_4228_, v___x_4243_);
lean_dec(v___x_4243_);
v___x_4245_ = lean_box(0);
lean_inc(v___x_4244_);
v___x_4246_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__0(v___x_4244_, v___x_4245_);
v___x_4247_ = l_Lean_MessageData_andList(v___x_4246_);
v___x_4248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__9);
v___x_4249_ = lean_array_get(v___x_4181_, v_snd_4224_, v___x_4233_);
lean_dec(v_snd_4224_);
v___x_4250_ = l_Lean_MessageData_ofConstName(v___x_4249_, v___x_4195_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set_tag(v___x_4226_, 7);
lean_ctor_set(v___x_4226_, 1, v___x_4250_);
lean_ctor_set(v___x_4226_, 0, v___x_4248_);
v___x_4252_ = v___x_4226_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v___x_4253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__11);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
lean_ctor_set(v___x_4255_, 1, v___x_4247_);
v___x_4256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13, &l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__13);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = l_List_lengthTR___redArg(v___x_4244_);
lean_dec(v___x_4244_);
v___x_4259_ = lean_nat_dec_eq(v___x_4258_, v___x_4228_);
lean_dec(v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__14));
v___y_4208_ = v___x_4257_;
v___y_4209_ = v_a_4242_;
v___y_4210_ = v_fst_4223_;
v___y_4211_ = v___x_4260_;
goto v___jp_4207_;
}
else
{
lean_object* v___x_4261_; 
v___x_4261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___closed__15));
v___y_4208_ = v___x_4257_;
v___y_4209_ = v_a_4242_;
v___y_4210_ = v_fst_4223_;
v___y_4211_ = v___x_4261_;
goto v___jp_4207_;
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_del_object(v___x_4226_);
lean_dec(v_snd_4224_);
lean_dec(v_fst_4223_);
v_a_4263_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4241_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4241_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_a_4272_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4221_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4221_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
v_a_4280_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4192_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4192_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed(lean_object* v_stx_4288_, lean_object* v___x_4289_, lean_object* v_cfg_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
uint8_t v_cfg_boxed_4300_; lean_object* v_res_4301_; 
v_cfg_boxed_4300_ = lean_unbox(v_cfg_4290_);
v_res_4301_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0(v_stx_4288_, v___x_4289_, v_cfg_boxed_4300_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___x_4289_);
lean_dec(v_stx_4288_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(lean_object* v_stx_4302_, uint8_t v_cfg_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___f_4315_; lean_object* v___x_4316_; 
v___x_4313_ = lean_box(0);
v___x_4314_ = lean_box(v_cfg_4303_);
v___f_4315_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4315_, 0, v_stx_4302_);
lean_closure_set(v___f_4315_, 1, v___x_4313_);
lean_closure_set(v___f_4315_, 2, v___x_4314_);
v___x_4316_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4315_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore___boxed(lean_object* v_stx_4317_, lean_object* v_cfg_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_){
_start:
{
uint8_t v_cfg_boxed_4328_; lean_object* v_res_4329_; 
v_cfg_boxed_4328_ = lean_unbox(v_cfg_4318_);
v_res_4329_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(v_stx_4317_, v_cfg_boxed_4328_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_);
lean_dec(v_a_4326_);
lean_dec_ref(v_a_4325_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(lean_object* v_ref_4330_, lean_object* v_msgData_4331_, uint8_t v_severity_4332_, uint8_t v_isSilent_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___redArg(v_ref_4330_, v_msgData_4331_, v_severity_4332_, v_isSilent_4333_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_4344_, lean_object* v_msgData_4345_, lean_object* v_severity_4346_, lean_object* v_isSilent_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
uint8_t v_severity_boxed_4357_; uint8_t v_isSilent_boxed_4358_; lean_object* v_res_4359_; 
v_severity_boxed_4357_ = lean_unbox(v_severity_4346_);
v_isSilent_boxed_4358_ = lean_unbox(v_isSilent_4347_);
v_res_4359_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore_spec__1_spec__1_spec__2(v_ref_4344_, v_msgData_4345_, v_severity_boxed_4357_, v_isSilent_boxed_4358_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v_ref_4344_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* v_stx_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; uint8_t v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; 
v___x_4370_ = lean_unsigned_to_nat(1u);
v___x_4371_ = l_Lean_Syntax_getArg(v_stx_4360_, v___x_4370_);
v___x_4372_ = 0;
v___x_4373_ = 1;
v___x_4374_ = l_Lean_Elab_Tactic_elabConstructorConfig___redArg(v___x_4371_, v___x_4372_, v___x_4373_, v_a_4361_, v_a_4367_, v_a_4368_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
v___x_4376_ = lean_unbox(v_a_4375_);
lean_dec(v_a_4375_);
v___x_4377_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructorCore(v_stx_4360_, v___x_4376_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
return v___x_4377_;
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_dec(v_stx_4360_);
v_a_4378_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4374_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4374_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* v_stx_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Elab_Tactic_evalConstructor(v_stx_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4410_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1));
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_4413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 10, 0);
v___x_4414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4410_, v___x_4411_, v___x_4412_, v___x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_4444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6));
v___x_4445_ = l_Lean_addBuiltinDeclarationRanges(v___x_4443_, v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* v_stx_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v___y_4459_; lean_object* v___x_4468_; uint8_t v_transparency_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; uint8_t v___x_4472_; uint8_t v___x_4473_; 
v___x_4468_ = l_Lean_Meta_Context_config(v_a_4453_);
v_transparency_4469_ = lean_ctor_get_uint8(v___x_4468_, 9);
lean_dec_ref(v___x_4468_);
v___x_4470_ = lean_unsigned_to_nat(1u);
v___x_4471_ = l_Lean_Syntax_getArg(v_stx_4448_, v___x_4470_);
v___x_4472_ = 2;
v___x_4473_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4469_, v___x_4472_);
if (v___x_4473_ == 0)
{
lean_object* v_keyedConfig_4474_; uint8_t v_trackZetaDelta_4475_; lean_object* v_zetaDeltaSet_4476_; lean_object* v_lctx_4477_; lean_object* v_localInstances_4478_; lean_object* v_defEqCtx_x3f_4479_; lean_object* v_synthPendingDepth_4480_; lean_object* v_customCanUnfoldPredicate_x3f_4481_; uint8_t v_univApprox_4482_; uint8_t v_inTypeClassResolution_4483_; uint8_t v_cacheInferType_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v_keyedConfig_4474_ = lean_ctor_get(v_a_4453_, 0);
v_trackZetaDelta_4475_ = lean_ctor_get_uint8(v_a_4453_, sizeof(void*)*7);
v_zetaDeltaSet_4476_ = lean_ctor_get(v_a_4453_, 1);
v_lctx_4477_ = lean_ctor_get(v_a_4453_, 2);
v_localInstances_4478_ = lean_ctor_get(v_a_4453_, 3);
v_defEqCtx_x3f_4479_ = lean_ctor_get(v_a_4453_, 4);
v_synthPendingDepth_4480_ = lean_ctor_get(v_a_4453_, 5);
v_customCanUnfoldPredicate_x3f_4481_ = lean_ctor_get(v_a_4453_, 6);
v_univApprox_4482_ = lean_ctor_get_uint8(v_a_4453_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4483_ = lean_ctor_get_uint8(v_a_4453_, sizeof(void*)*7 + 2);
v_cacheInferType_4484_ = lean_ctor_get_uint8(v_a_4453_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4474_);
v___x_4485_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4472_, v_keyedConfig_4474_);
lean_inc(v_customCanUnfoldPredicate_x3f_4481_);
lean_inc(v_synthPendingDepth_4480_);
lean_inc(v_defEqCtx_x3f_4479_);
lean_inc_ref(v_localInstances_4478_);
lean_inc_ref(v_lctx_4477_);
lean_inc(v_zetaDeltaSet_4476_);
v___x_4486_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
lean_ctor_set(v___x_4486_, 1, v_zetaDeltaSet_4476_);
lean_ctor_set(v___x_4486_, 2, v_lctx_4477_);
lean_ctor_set(v___x_4486_, 3, v_localInstances_4478_);
lean_ctor_set(v___x_4486_, 4, v_defEqCtx_x3f_4479_);
lean_ctor_set(v___x_4486_, 5, v_synthPendingDepth_4480_);
lean_ctor_set(v___x_4486_, 6, v_customCanUnfoldPredicate_x3f_4481_);
lean_ctor_set_uint8(v___x_4486_, sizeof(void*)*7, v_trackZetaDelta_4475_);
lean_ctor_set_uint8(v___x_4486_, sizeof(void*)*7 + 1, v_univApprox_4482_);
lean_ctor_set_uint8(v___x_4486_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4483_);
lean_ctor_set_uint8(v___x_4486_, sizeof(void*)*7 + 3, v_cacheInferType_4484_);
v___x_4487_ = l_Lean_Elab_Tactic_evalTactic(v___x_4471_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v___x_4486_, v_a_4454_, v_a_4455_, v_a_4456_);
lean_dec_ref_known(v___x_4486_, 7);
v___y_4459_ = v___x_4487_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_Elab_Tactic_evalTactic(v___x_4471_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
v___y_4459_ = v___x_4488_;
goto v___jp_4458_;
}
v___jp_4458_:
{
if (lean_obj_tag(v___y_4459_) == 0)
{
return v___y_4459_;
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
v_a_4460_ = lean_ctor_get(v___y_4459_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___y_4459_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___y_4459_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___y_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object* v_stx_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Lean_Elab_Tactic_evalWithReducible(v_stx_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4492_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_stx_4489_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4513_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1));
v___x_4515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_4516_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
v___x_4517_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4513_, v___x_4514_, v___x_4515_, v___x_4516_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_4547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6));
v___x_4548_ = l_Lean_addBuiltinDeclarationRanges(v___x_4546_, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* v_stx_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v___y_4562_; lean_object* v___x_4571_; uint8_t v_transparency_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; uint8_t v___x_4576_; 
v___x_4571_ = l_Lean_Meta_Context_config(v_a_4556_);
v_transparency_4572_ = lean_ctor_get_uint8(v___x_4571_, 9);
lean_dec_ref(v___x_4571_);
v___x_4573_ = lean_unsigned_to_nat(1u);
v___x_4574_ = l_Lean_Syntax_getArg(v_stx_4551_, v___x_4573_);
v___x_4575_ = 3;
v___x_4576_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4572_, v___x_4575_);
if (v___x_4576_ == 0)
{
lean_object* v_keyedConfig_4577_; uint8_t v_trackZetaDelta_4578_; lean_object* v_zetaDeltaSet_4579_; lean_object* v_lctx_4580_; lean_object* v_localInstances_4581_; lean_object* v_defEqCtx_x3f_4582_; lean_object* v_synthPendingDepth_4583_; lean_object* v_customCanUnfoldPredicate_x3f_4584_; uint8_t v_univApprox_4585_; uint8_t v_inTypeClassResolution_4586_; uint8_t v_cacheInferType_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v_keyedConfig_4577_ = lean_ctor_get(v_a_4556_, 0);
v_trackZetaDelta_4578_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*7);
v_zetaDeltaSet_4579_ = lean_ctor_get(v_a_4556_, 1);
v_lctx_4580_ = lean_ctor_get(v_a_4556_, 2);
v_localInstances_4581_ = lean_ctor_get(v_a_4556_, 3);
v_defEqCtx_x3f_4582_ = lean_ctor_get(v_a_4556_, 4);
v_synthPendingDepth_4583_ = lean_ctor_get(v_a_4556_, 5);
v_customCanUnfoldPredicate_x3f_4584_ = lean_ctor_get(v_a_4556_, 6);
v_univApprox_4585_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4586_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*7 + 2);
v_cacheInferType_4587_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4577_);
v___x_4588_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4575_, v_keyedConfig_4577_);
lean_inc(v_customCanUnfoldPredicate_x3f_4584_);
lean_inc(v_synthPendingDepth_4583_);
lean_inc(v_defEqCtx_x3f_4582_);
lean_inc_ref(v_localInstances_4581_);
lean_inc_ref(v_lctx_4580_);
lean_inc(v_zetaDeltaSet_4579_);
v___x_4589_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
lean_ctor_set(v___x_4589_, 1, v_zetaDeltaSet_4579_);
lean_ctor_set(v___x_4589_, 2, v_lctx_4580_);
lean_ctor_set(v___x_4589_, 3, v_localInstances_4581_);
lean_ctor_set(v___x_4589_, 4, v_defEqCtx_x3f_4582_);
lean_ctor_set(v___x_4589_, 5, v_synthPendingDepth_4583_);
lean_ctor_set(v___x_4589_, 6, v_customCanUnfoldPredicate_x3f_4584_);
lean_ctor_set_uint8(v___x_4589_, sizeof(void*)*7, v_trackZetaDelta_4578_);
lean_ctor_set_uint8(v___x_4589_, sizeof(void*)*7 + 1, v_univApprox_4585_);
lean_ctor_set_uint8(v___x_4589_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4586_);
lean_ctor_set_uint8(v___x_4589_, sizeof(void*)*7 + 3, v_cacheInferType_4587_);
v___x_4590_ = l_Lean_Elab_Tactic_evalTactic(v___x_4574_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v___x_4589_, v_a_4557_, v_a_4558_, v_a_4559_);
lean_dec_ref_known(v___x_4589_, 7);
v___y_4562_ = v___x_4590_;
goto v___jp_4561_;
}
else
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Lean_Elab_Tactic_evalTactic(v___x_4574_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
v___y_4562_ = v___x_4591_;
goto v___jp_4561_;
}
v___jp_4561_:
{
if (lean_obj_tag(v___y_4562_) == 0)
{
return v___y_4562_;
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
v_a_4563_ = lean_ctor_get(v___y_4562_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___y_4562_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___y_4562_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___y_4562_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object* v_stx_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(v_stx_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_stx_4592_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4616_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1));
v___x_4618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_4619_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
v___x_4620_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4616_, v___x_4617_, v___x_4618_, v___x_4619_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_4650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6));
v___x_4651_ = l_Lean_addBuiltinDeclarationRanges(v___x_4649_, v___x_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit(lean_object* v_stx_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v___y_4665_; lean_object* v___x_4674_; uint8_t v_transparency_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; uint8_t v___x_4679_; 
v___x_4674_ = l_Lean_Meta_Context_config(v_a_4659_);
v_transparency_4675_ = lean_ctor_get_uint8(v___x_4674_, 9);
lean_dec_ref(v___x_4674_);
v___x_4676_ = lean_unsigned_to_nat(1u);
v___x_4677_ = l_Lean_Syntax_getArg(v_stx_4654_, v___x_4676_);
v___x_4678_ = 5;
v___x_4679_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4675_, v___x_4678_);
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
v___x_4691_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4678_, v_keyedConfig_4680_);
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
v___x_4693_ = l_Lean_Elab_Tactic_evalTactic(v___x_4677_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v___x_4692_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec_ref_known(v___x_4692_, 7);
v___y_4665_ = v___x_4693_;
goto v___jp_4664_;
}
else
{
lean_object* v___x_4694_; 
v___x_4694_ = l_Lean_Elab_Tactic_evalTactic(v___x_4677_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit___boxed(lean_object* v_stx_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Lean_Elab_Tactic_evalWithImplicit(v_stx_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1(){
_start:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4719_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1));
v___x_4721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3));
v___x_4722_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithImplicit___boxed), 10, 0);
v___x_4723_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4719_, v___x_4720_, v___x_4721_, v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___boxed(lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* v_stx_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v___y_4737_; lean_object* v___x_4746_; uint8_t v_transparency_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v___x_4746_ = l_Lean_Meta_Context_config(v_a_4731_);
v_transparency_4747_ = lean_ctor_get_uint8(v___x_4746_, 9);
lean_dec_ref(v___x_4746_);
v___x_4748_ = 0;
v___x_4749_ = lean_unsigned_to_nat(1u);
v___x_4750_ = l_Lean_Syntax_getArg(v_stx_4726_, v___x_4749_);
v___x_4751_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4747_, v___x_4748_);
if (v___x_4751_ == 0)
{
lean_object* v_keyedConfig_4752_; uint8_t v_trackZetaDelta_4753_; lean_object* v_zetaDeltaSet_4754_; lean_object* v_lctx_4755_; lean_object* v_localInstances_4756_; lean_object* v_defEqCtx_x3f_4757_; lean_object* v_synthPendingDepth_4758_; lean_object* v_customCanUnfoldPredicate_x3f_4759_; uint8_t v_univApprox_4760_; uint8_t v_inTypeClassResolution_4761_; uint8_t v_cacheInferType_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v_keyedConfig_4752_ = lean_ctor_get(v_a_4731_, 0);
v_trackZetaDelta_4753_ = lean_ctor_get_uint8(v_a_4731_, sizeof(void*)*7);
v_zetaDeltaSet_4754_ = lean_ctor_get(v_a_4731_, 1);
v_lctx_4755_ = lean_ctor_get(v_a_4731_, 2);
v_localInstances_4756_ = lean_ctor_get(v_a_4731_, 3);
v_defEqCtx_x3f_4757_ = lean_ctor_get(v_a_4731_, 4);
v_synthPendingDepth_4758_ = lean_ctor_get(v_a_4731_, 5);
v_customCanUnfoldPredicate_x3f_4759_ = lean_ctor_get(v_a_4731_, 6);
v_univApprox_4760_ = lean_ctor_get_uint8(v_a_4731_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4761_ = lean_ctor_get_uint8(v_a_4731_, sizeof(void*)*7 + 2);
v_cacheInferType_4762_ = lean_ctor_get_uint8(v_a_4731_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4752_);
v___x_4763_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4748_, v_keyedConfig_4752_);
lean_inc(v_customCanUnfoldPredicate_x3f_4759_);
lean_inc(v_synthPendingDepth_4758_);
lean_inc(v_defEqCtx_x3f_4757_);
lean_inc_ref(v_localInstances_4756_);
lean_inc_ref(v_lctx_4755_);
lean_inc(v_zetaDeltaSet_4754_);
v___x_4764_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
lean_ctor_set(v___x_4764_, 1, v_zetaDeltaSet_4754_);
lean_ctor_set(v___x_4764_, 2, v_lctx_4755_);
lean_ctor_set(v___x_4764_, 3, v_localInstances_4756_);
lean_ctor_set(v___x_4764_, 4, v_defEqCtx_x3f_4757_);
lean_ctor_set(v___x_4764_, 5, v_synthPendingDepth_4758_);
lean_ctor_set(v___x_4764_, 6, v_customCanUnfoldPredicate_x3f_4759_);
lean_ctor_set_uint8(v___x_4764_, sizeof(void*)*7, v_trackZetaDelta_4753_);
lean_ctor_set_uint8(v___x_4764_, sizeof(void*)*7 + 1, v_univApprox_4760_);
lean_ctor_set_uint8(v___x_4764_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4761_);
lean_ctor_set_uint8(v___x_4764_, sizeof(void*)*7 + 3, v_cacheInferType_4762_);
v___x_4765_ = l_Lean_Elab_Tactic_evalTactic(v___x_4750_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v___x_4764_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec_ref_known(v___x_4764_, 7);
v___y_4737_ = v___x_4765_;
goto v___jp_4736_;
}
else
{
lean_object* v___x_4766_; 
v___x_4766_ = l_Lean_Elab_Tactic_evalTactic(v___x_4750_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
v___y_4737_ = v___x_4766_;
goto v___jp_4736_;
}
v___jp_4736_:
{
if (lean_obj_tag(v___y_4737_) == 0)
{
return v___y_4737_;
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
v_a_4738_ = lean_ctor_get(v___y_4737_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___y_4737_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___y_4737_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___y_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object* v_stx_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_Elab_Tactic_evalWithUnfoldingAll(v_stx_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_stx_4767_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4791_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1));
v___x_4793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_4794_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
v___x_4795_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4791_, v___x_4792_, v___x_4793_, v___x_4794_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object* v_a_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_4825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6));
v___x_4826_ = l_Lean_addBuiltinDeclarationRanges(v___x_4824_, v___x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object* v_stx_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v___y_4840_; lean_object* v___x_4849_; uint8_t v_transparency_4850_; uint8_t v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4849_ = l_Lean_Meta_Context_config(v_a_4834_);
v_transparency_4850_ = lean_ctor_get_uint8(v___x_4849_, 9);
lean_dec_ref(v___x_4849_);
v___x_4851_ = 4;
v___x_4852_ = lean_unsigned_to_nat(1u);
v___x_4853_ = l_Lean_Syntax_getArg(v_stx_4829_, v___x_4852_);
v___x_4854_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4850_, v___x_4851_);
if (v___x_4854_ == 0)
{
lean_object* v_keyedConfig_4855_; uint8_t v_trackZetaDelta_4856_; lean_object* v_zetaDeltaSet_4857_; lean_object* v_lctx_4858_; lean_object* v_localInstances_4859_; lean_object* v_defEqCtx_x3f_4860_; lean_object* v_synthPendingDepth_4861_; lean_object* v_customCanUnfoldPredicate_x3f_4862_; uint8_t v_univApprox_4863_; uint8_t v_inTypeClassResolution_4864_; uint8_t v_cacheInferType_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v_keyedConfig_4855_ = lean_ctor_get(v_a_4834_, 0);
v_trackZetaDelta_4856_ = lean_ctor_get_uint8(v_a_4834_, sizeof(void*)*7);
v_zetaDeltaSet_4857_ = lean_ctor_get(v_a_4834_, 1);
v_lctx_4858_ = lean_ctor_get(v_a_4834_, 2);
v_localInstances_4859_ = lean_ctor_get(v_a_4834_, 3);
v_defEqCtx_x3f_4860_ = lean_ctor_get(v_a_4834_, 4);
v_synthPendingDepth_4861_ = lean_ctor_get(v_a_4834_, 5);
v_customCanUnfoldPredicate_x3f_4862_ = lean_ctor_get(v_a_4834_, 6);
v_univApprox_4863_ = lean_ctor_get_uint8(v_a_4834_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4864_ = lean_ctor_get_uint8(v_a_4834_, sizeof(void*)*7 + 2);
v_cacheInferType_4865_ = lean_ctor_get_uint8(v_a_4834_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4855_);
v___x_4866_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4851_, v_keyedConfig_4855_);
lean_inc(v_customCanUnfoldPredicate_x3f_4862_);
lean_inc(v_synthPendingDepth_4861_);
lean_inc(v_defEqCtx_x3f_4860_);
lean_inc_ref(v_localInstances_4859_);
lean_inc_ref(v_lctx_4858_);
lean_inc(v_zetaDeltaSet_4857_);
v___x_4867_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4867_, 0, v___x_4866_);
lean_ctor_set(v___x_4867_, 1, v_zetaDeltaSet_4857_);
lean_ctor_set(v___x_4867_, 2, v_lctx_4858_);
lean_ctor_set(v___x_4867_, 3, v_localInstances_4859_);
lean_ctor_set(v___x_4867_, 4, v_defEqCtx_x3f_4860_);
lean_ctor_set(v___x_4867_, 5, v_synthPendingDepth_4861_);
lean_ctor_set(v___x_4867_, 6, v_customCanUnfoldPredicate_x3f_4862_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*7, v_trackZetaDelta_4856_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*7 + 1, v_univApprox_4863_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4864_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*7 + 3, v_cacheInferType_4865_);
v___x_4868_ = l_Lean_Elab_Tactic_evalTactic(v___x_4853_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v___x_4867_, v_a_4835_, v_a_4836_, v_a_4837_);
lean_dec_ref_known(v___x_4867_, 7);
v___y_4840_ = v___x_4868_;
goto v___jp_4839_;
}
else
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Lean_Elab_Tactic_evalTactic(v___x_4853_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
v___y_4840_ = v___x_4869_;
goto v___jp_4839_;
}
v___jp_4839_:
{
if (lean_obj_tag(v___y_4840_) == 0)
{
return v___y_4840_;
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
v_a_4841_ = lean_ctor_get(v___y_4840_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___y_4840_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___y_4840_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___y_4840_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object* v_stx_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Elab_Tactic_evalWithUnfoldingNone(v_stx_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4875_);
lean_dec(v_a_4874_);
lean_dec_ref(v_a_4873_);
lean_dec(v_a_4872_);
lean_dec_ref(v_a_4871_);
lean_dec(v_stx_4870_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1(){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4894_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1));
v___x_4896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3));
v___x_4897_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed), 10, 0);
v___x_4898_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4894_, v___x_4895_, v___x_4896_, v___x_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object* v_a_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object* v_stx_4904_, lean_object* v___x_4905_, uint8_t v___x_4906_, lean_object* v_userName_x3f_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Elab_Tactic_elabTerm(v_stx_4904_, v___x_4905_, v___x_4906_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_5004_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_5004_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_5004_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
if (lean_obj_tag(v_a_4918_) == 1)
{
lean_object* v_fvarId_4922_; lean_object* v___x_4924_; 
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v_userName_x3f_4907_);
v_fvarId_4922_ = lean_ctor_get(v_a_4918_, 0);
lean_inc(v_fvarId_4922_);
lean_dec_ref_known(v_a_4918_, 1);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v_fvarId_4922_);
v___x_4924_ = v___x_4920_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_fvarId_4922_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
else
{
lean_object* v___x_4926_; 
lean_del_object(v___x_4920_);
lean_inc(v___y_4915_);
lean_inc_ref(v___y_4914_);
lean_inc(v___y_4913_);
lean_inc_ref(v___y_4912_);
lean_inc(v_a_4918_);
v___x_4926_ = lean_infer_type(v_a_4918_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v_userName_4929_; uint8_t v_preserveBinderNames_4930_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc(v_a_4927_);
lean_dec_ref_known(v___x_4926_, 1);
if (lean_obj_tag(v_userName_x3f_4907_) == 0)
{
lean_object* v___x_4993_; 
v___x_4993_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1));
v_userName_4929_ = v___x_4993_;
v_preserveBinderNames_4930_ = v___x_4906_;
v___y_4931_ = v___y_4909_;
v___y_4932_ = v___y_4912_;
v___y_4933_ = v___y_4913_;
v___y_4934_ = v___y_4914_;
v___y_4935_ = v___y_4915_;
goto v___jp_4928_;
}
else
{
lean_object* v_val_4994_; uint8_t v___x_4995_; 
v_val_4994_ = lean_ctor_get(v_userName_x3f_4907_, 0);
lean_inc(v_val_4994_);
lean_dec_ref_known(v_userName_x3f_4907_, 1);
v___x_4995_ = 1;
v_userName_4929_ = v_val_4994_;
v_preserveBinderNames_4930_ = v___x_4995_;
v___y_4931_ = v___y_4909_;
v___y_4932_ = v___y_4912_;
v___y_4933_ = v___y_4913_;
v___y_4934_ = v___y_4914_;
v___y_4935_ = v___y_4915_;
goto v___jp_4928_;
}
v___jp_4928_:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4938_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___x_4938_ = l_Lean_MVarId_assert(v_a_4937_, v_userName_4929_, v_a_4927_, v_a_4918_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4940_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v___x_4940_ = l_Lean_Meta_intro1Core(v_a_4939_, v_preserveBinderNames_4930_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; lean_object* v_fst_4942_; lean_object* v_snd_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4968_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
lean_inc(v_a_4941_);
lean_dec_ref_known(v___x_4940_, 1);
v_fst_4942_ = lean_ctor_get(v_a_4941_, 0);
v_snd_4943_ = lean_ctor_get(v_a_4941_, 1);
v_isSharedCheck_4968_ = !lean_is_exclusive(v_a_4941_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4945_ = v_a_4941_;
v_isShared_4946_ = v_isSharedCheck_4968_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_snd_4943_);
lean_inc(v_fst_4942_);
lean_dec(v_a_4941_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4968_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4947_ = lean_box(0);
if (v_isShared_4946_ == 0)
{
lean_ctor_set_tag(v___x_4945_, 1);
lean_ctor_set(v___x_4945_, 1, v___x_4947_);
lean_ctor_set(v___x_4945_, 0, v_snd_4943_);
v___x_4949_ = v___x_4945_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_snd_4943_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4949_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v___x_4950_, 0);
lean_dec(v_unused_4958_);
v___x_4952_ = v___x_4950_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_dec(v___x_4950_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 0, v_fst_4942_);
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_fst_4942_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v_fst_4942_);
v_a_4959_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4950_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4950_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
v_a_4969_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4940_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4940_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
v_a_4977_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4938_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4938_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v_userName_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4918_);
v_a_4985_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4936_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4936_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
lean_dec(v_a_4918_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v_userName_x3f_4907_);
v_a_4996_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4926_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4926_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v_userName_x3f_4907_);
v_a_5005_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4917_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4917_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object* v_stx_5013_, lean_object* v___x_5014_, lean_object* v___x_5015_, lean_object* v_userName_x3f_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
uint8_t v___x_1499__boxed_5026_; lean_object* v_res_5027_; 
v___x_1499__boxed_5026_ = lean_unbox(v___x_5015_);
v_res_5027_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0(v_stx_5013_, v___x_5014_, v___x_1499__boxed_5026_, v_userName_x3f_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* v_stx_5028_, lean_object* v_userName_x3f_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v___x_5039_; uint8_t v___x_5040_; lean_object* v___x_5041_; lean_object* v___f_5042_; lean_object* v___x_5043_; 
v___x_5039_ = lean_box(0);
v___x_5040_ = 0;
v___x_5041_ = lean_box(v___x_5040_);
v___f_5042_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed), 13, 4);
lean_closure_set(v___f_5042_, 0, v_stx_5028_);
lean_closure_set(v___f_5042_, 1, v___x_5039_);
lean_closure_set(v___f_5042_, 2, v___x_5041_);
lean_closure_set(v___f_5042_, 3, v_userName_x3f_5029_);
v___x_5043_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5042_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object* v_stx_5044_, lean_object* v_userName_x3f_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Elab_Tactic_elabAsFVar(v_stx_5044_, v_userName_x3f_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
lean_dec(v_a_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object* v_k_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
lean_object* v___x_5066_; 
lean_inc(v___y_5060_);
lean_inc_ref(v___y_5059_);
lean_inc(v___y_5058_);
lean_inc_ref(v___y_5057_);
v___x_5066_ = lean_apply_9(v_k_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, lean_box(0));
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object* v_k_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(v_k_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object* v_k_5078_, uint8_t v_allowLevelAssignments_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v___f_5089_; lean_object* v___x_5090_; 
lean_inc(v___y_5083_);
lean_inc_ref(v___y_5082_);
lean_inc(v___y_5081_);
lean_inc_ref(v___y_5080_);
v___f_5089_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5089_, 0, v_k_5078_);
lean_closure_set(v___f_5089_, 1, v___y_5080_);
lean_closure_set(v___f_5089_, 2, v___y_5081_);
lean_closure_set(v___f_5089_, 3, v___y_5082_);
lean_closure_set(v___f_5089_, 4, v___y_5083_);
v___x_5090_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_5079_, v___f_5089_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
if (lean_obj_tag(v___x_5090_) == 0)
{
return v___x_5090_;
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5090_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5090_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object* v_k_5099_, lean_object* v_allowLevelAssignments_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5110_; lean_object* v_res_5111_; 
v_allowLevelAssignments_boxed_5110_ = lean_unbox(v_allowLevelAssignments_5100_);
v_res_5111_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_5099_, v_allowLevelAssignments_boxed_5110_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object* v_00_u03b1_5112_, lean_object* v_k_5113_, uint8_t v_allowLevelAssignments_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_5113_, v_allowLevelAssignments_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object* v_00_u03b1_5125_, lean_object* v_k_5126_, lean_object* v_allowLevelAssignments_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5137_; lean_object* v_res_5138_; 
v_allowLevelAssignments_boxed_5137_ = lean_unbox(v_allowLevelAssignments_5127_);
v_res_5138_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(v_00_u03b1_5125_, v_k_5126_, v_allowLevelAssignments_boxed_5137_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec_ref(v___y_5132_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object* v_a_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v_a_x3f_5147_){
_start:
{
uint8_t v___x_5149_; lean_object* v___x_5150_; 
v___x_5149_ = 0;
v___x_5150_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_5139_, v___x_5149_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object* v_a_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v_a_x3f_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v_a_x3f_5159_);
lean_dec(v_a_x3f_5159_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object* v_x_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_){
_start:
{
lean_object* v___x_5172_; 
v___x_5172_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_5164_, v___y_5166_, v___y_5168_, v___y_5170_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v_r_5174_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref_known(v___x_5172_, 1);
lean_inc(v___y_5170_);
lean_inc_ref(v___y_5169_);
lean_inc(v___y_5168_);
lean_inc_ref(v___y_5167_);
lean_inc(v___y_5166_);
lean_inc_ref(v___y_5165_);
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
v_r_5174_ = lean_apply_9(v_x_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, lean_box(0));
if (lean_obj_tag(v_r_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5199_; 
v_a_5175_ = lean_ctor_get(v_r_5174_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v_r_5174_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5177_ = v_r_5174_;
v_isShared_5178_ = v_isSharedCheck_5199_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v_r_5174_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5199_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
lean_inc(v_a_5175_);
if (v_isShared_5178_ == 0)
{
lean_ctor_set_tag(v___x_5177_, 1);
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5173_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___x_5180_);
lean_dec_ref(v___x_5180_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5188_; 
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5188_ == 0)
{
lean_object* v_unused_5189_; 
v_unused_5189_ = lean_ctor_get(v___x_5181_, 0);
lean_dec(v_unused_5189_);
v___x_5183_ = v___x_5181_;
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
else
{
lean_dec(v___x_5181_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5186_; 
if (v_isShared_5184_ == 0)
{
lean_ctor_set(v___x_5183_, 0, v_a_5175_);
v___x_5186_ = v___x_5183_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5175_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_a_5175_);
v_a_5190_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5181_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5181_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
}
else
{
lean_object* v_a_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v_a_5200_ = lean_ctor_get(v_r_5174_, 0);
lean_inc(v_a_5200_);
lean_dec_ref_known(v_r_5174_, 1);
v___x_5201_ = lean_box(0);
v___x_5202_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_5173_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___x_5201_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5209_ == 0)
{
lean_object* v_unused_5210_; 
v_unused_5210_ = lean_ctor_get(v___x_5202_, 0);
lean_dec(v_unused_5210_);
v___x_5204_ = v___x_5202_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_dec(v___x_5202_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
lean_ctor_set_tag(v___x_5204_, 1);
lean_ctor_set(v___x_5204_, 0, v_a_5200_);
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5200_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_dec(v_a_5200_);
v_a_5211_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5202_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5202_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5226_; 
lean_dec_ref(v_x_5162_);
v_a_5219_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5221_ = v___x_5172_;
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5172_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object* v_x_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object* v_00_u03b1_5238_, lean_object* v_x_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; 
v___x_5249_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object* v_00_u03b1_5250_, lean_object* v_x_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(v_00_u03b1_5250_, v_x_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object* v_a_5262_, uint8_t v___x_5263_, lean_object* v_as_5264_, lean_object* v_i_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
lean_object* v_zero_5271_; uint8_t v_isZero_5272_; 
v_zero_5271_ = lean_unsigned_to_nat(0u);
v_isZero_5272_ = lean_nat_dec_eq(v_i_5265_, v_zero_5271_);
if (v_isZero_5272_ == 1)
{
lean_object* v___x_5273_; lean_object* v___x_5274_; 
lean_dec(v_i_5265_);
lean_dec_ref(v_a_5262_);
v___x_5273_ = lean_box(0);
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
return v___x_5274_;
}
else
{
lean_object* v_one_5275_; lean_object* v_n_5276_; lean_object* v___x_5277_; 
v_one_5275_ = lean_unsigned_to_nat(1u);
v_n_5276_ = lean_nat_sub(v_i_5265_, v_one_5275_);
lean_dec(v_i_5265_);
v___x_5277_ = lean_array_fget(v_as_5264_, v_n_5276_);
if (lean_obj_tag(v___x_5277_) == 0)
{
v_i_5265_ = v_n_5276_;
goto _start;
}
else
{
lean_object* v_val_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5310_; 
v_val_5279_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5281_ = v___x_5277_;
v_isShared_5282_ = v_isSharedCheck_5310_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_val_5279_);
lean_dec(v___x_5277_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5310_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5283_ = l_Lean_LocalDecl_type(v_val_5279_);
lean_inc_ref(v_a_5262_);
v___x_5284_ = l_Lean_Meta_isExprDefEq(v_a_5262_, v___x_5283_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5301_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5287_ = v___x_5284_;
v_isShared_5288_ = v_isSharedCheck_5301_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5284_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5301_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
uint8_t v___x_5289_; 
v___x_5289_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5279_);
if (v___x_5289_ == 0)
{
if (v___x_5263_ == 0)
{
lean_del_object(v___x_5287_);
lean_dec(v_a_5285_);
lean_del_object(v___x_5281_);
lean_dec(v_val_5279_);
v_i_5265_ = v_n_5276_;
goto _start;
}
else
{
uint8_t v___x_5291_; 
v___x_5291_ = lean_unbox(v_a_5285_);
lean_dec(v_a_5285_);
if (v___x_5291_ == 0)
{
lean_del_object(v___x_5287_);
lean_del_object(v___x_5281_);
lean_dec(v_val_5279_);
v_i_5265_ = v_n_5276_;
goto _start;
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5295_; 
lean_dec(v_n_5276_);
lean_dec_ref(v_a_5262_);
v___x_5293_ = l_Lean_LocalDecl_fvarId(v_val_5279_);
lean_dec(v_val_5279_);
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 0, v___x_5293_);
v___x_5295_ = v___x_5281_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v___x_5293_);
v___x_5295_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
lean_object* v___x_5297_; 
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5295_);
v___x_5297_ = v___x_5287_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
}
}
else
{
lean_del_object(v___x_5287_);
lean_dec(v_a_5285_);
lean_del_object(v___x_5281_);
lean_dec(v_val_5279_);
v_i_5265_ = v_n_5276_;
goto _start;
}
}
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_del_object(v___x_5281_);
lean_dec(v_val_5279_);
lean_dec(v_n_5276_);
lean_dec_ref(v_a_5262_);
v_a_5302_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5284_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5284_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_a_5311_, lean_object* v___x_5312_, lean_object* v_as_5313_, lean_object* v_i_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
uint8_t v___x_6449__boxed_5320_; lean_object* v_res_5321_; 
v___x_6449__boxed_5320_ = lean_unbox(v___x_5312_);
v_res_5321_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5311_, v___x_6449__boxed_5320_, v_as_5313_, v_i_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
lean_dec_ref(v_as_5313_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_5322_, uint8_t v___x_5323_, lean_object* v_as_5324_, lean_object* v_i_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
lean_object* v_zero_5335_; uint8_t v_isZero_5336_; 
v_zero_5335_ = lean_unsigned_to_nat(0u);
v_isZero_5336_ = lean_nat_dec_eq(v_i_5325_, v_zero_5335_);
if (v_isZero_5336_ == 1)
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
lean_dec(v_i_5325_);
lean_dec_ref(v_a_5322_);
v___x_5337_ = lean_box(0);
v___x_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5337_);
return v___x_5338_;
}
else
{
lean_object* v_one_5339_; lean_object* v_n_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v_one_5339_ = lean_unsigned_to_nat(1u);
v_n_5340_ = lean_nat_sub(v_i_5325_, v_one_5339_);
lean_dec(v_i_5325_);
v___x_5341_ = lean_array_fget_borrowed(v_as_5324_, v_n_5340_);
lean_inc_ref(v_a_5322_);
v___x_5342_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5322_, v___x_5323_, v___x_5341_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
lean_inc(v_a_5343_);
if (lean_obj_tag(v_a_5343_) == 0)
{
lean_dec_ref_known(v___x_5342_, 1);
v_i_5325_ = v_n_5340_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_5343_, 1);
lean_dec(v_n_5340_);
lean_dec_ref(v_a_5322_);
return v___x_5342_;
}
}
else
{
lean_dec(v_n_5340_);
lean_dec_ref(v_a_5322_);
return v___x_5342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object* v_a_5345_, uint8_t v___x_5346_, lean_object* v_x_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
if (lean_obj_tag(v_x_5347_) == 0)
{
lean_object* v_cs_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v_cs_5357_ = lean_ctor_get(v_x_5347_, 0);
v___x_5358_ = lean_array_get_size(v_cs_5357_);
v___x_5359_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5345_, v___x_5346_, v_cs_5357_, v___x_5358_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
return v___x_5359_;
}
else
{
lean_object* v_vs_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v_vs_5360_ = lean_ctor_get(v_x_5347_, 0);
v___x_5361_ = lean_array_get_size(v_vs_5360_);
v___x_5362_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5345_, v___x_5346_, v_vs_5360_, v___x_5361_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
return v___x_5362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object* v_a_5363_, lean_object* v___x_5364_, lean_object* v_x_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
uint8_t v___x_6544__boxed_5375_; lean_object* v_res_5376_; 
v___x_6544__boxed_5375_ = lean_unbox(v___x_5364_);
v_res_5376_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5363_, v___x_6544__boxed_5375_, v_x_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_dec_ref(v___y_5368_);
lean_dec(v___y_5367_);
lean_dec_ref(v___y_5366_);
lean_dec_ref(v_x_5365_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_5377_, lean_object* v___x_5378_, lean_object* v_as_5379_, lean_object* v_i_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
uint8_t v___x_6562__boxed_5390_; lean_object* v_res_5391_; 
v___x_6562__boxed_5390_ = lean_unbox(v___x_5378_);
v_res_5391_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5377_, v___x_6562__boxed_5390_, v_as_5379_, v_i_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec_ref(v_as_5379_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object* v_a_5392_, uint8_t v___x_5393_, lean_object* v_t_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v_root_5404_; lean_object* v_tail_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v_root_5404_ = lean_ctor_get(v_t_5394_, 0);
v_tail_5405_ = lean_ctor_get(v_t_5394_, 1);
v___x_5406_ = lean_array_get_size(v_tail_5405_);
lean_inc_ref(v_a_5392_);
v___x_5407_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5392_, v___x_5393_, v_tail_5405_, v___x_5406_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v_a_5408_; 
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
lean_inc(v_a_5408_);
if (lean_obj_tag(v_a_5408_) == 0)
{
lean_object* v___x_5409_; 
lean_dec_ref_known(v___x_5407_, 1);
v___x_5409_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_5392_, v___x_5393_, v_root_5404_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
return v___x_5409_;
}
else
{
lean_dec_ref_known(v_a_5408_, 1);
lean_dec_ref(v_a_5392_);
return v___x_5407_;
}
}
else
{
lean_dec_ref(v_a_5392_);
return v___x_5407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object* v_a_5410_, lean_object* v___x_5411_, lean_object* v_t_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
uint8_t v___x_6641__boxed_5422_; lean_object* v_res_5423_; 
v___x_6641__boxed_5422_ = lean_unbox(v___x_5411_);
v_res_5423_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_5410_, v___x_6641__boxed_5422_, v_t_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec_ref(v_t_5412_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object* v_a_5424_, uint8_t v___x_5425_, lean_object* v_lctx_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
lean_object* v_decls_5436_; lean_object* v___x_5437_; 
v_decls_5436_ = lean_ctor_get(v_lctx_5426_, 1);
v___x_5437_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_5424_, v___x_5425_, v_decls_5436_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object* v_a_5438_, lean_object* v___x_5439_, lean_object* v_lctx_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
uint8_t v___x_6684__boxed_5450_; lean_object* v_res_5451_; 
v___x_6684__boxed_5450_ = lean_unbox(v___x_5439_);
v_res_5451_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_5438_, v___x_6684__boxed_5450_, v_lctx_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec_ref(v_lctx_5440_);
return v_res_5451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0));
v___x_5454_ = l_Lean_stringToMessageData(v___x_5453_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object* v___x_5455_, lean_object* v___x_5456_, uint8_t v___x_5457_, uint8_t v___x_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v___x_5468_; 
v___x_5468_ = l_Lean_Elab_Tactic_elabTerm(v___x_5455_, v___x_5456_, v___x_5457_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v_a_5469_; lean_object* v_lctx_5470_; lean_object* v___x_5471_; 
v_a_5469_ = lean_ctor_get(v___x_5468_, 0);
lean_inc_n(v_a_5469_, 2);
lean_dec_ref_known(v___x_5468_, 1);
v_lctx_5470_ = lean_ctor_get(v___y_5463_, 2);
v___x_5471_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_5469_, v___x_5458_, v_lctx_5470_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5484_; 
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5474_ = v___x_5471_;
v_isShared_5475_ = v_isSharedCheck_5484_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5471_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5484_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
if (lean_obj_tag(v_a_5472_) == 0)
{
lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; 
lean_del_object(v___x_5474_);
v___x_5476_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRename___lam__0___closed__1, &l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1);
v___x_5477_ = l_Lean_indentExpr(v_a_5469_);
v___x_5478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5478_, 0, v___x_5476_);
lean_ctor_set(v___x_5478_, 1, v___x_5477_);
v___x_5479_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_5478_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
return v___x_5479_;
}
else
{
lean_object* v_val_5480_; lean_object* v___x_5482_; 
lean_dec(v_a_5469_);
v_val_5480_ = lean_ctor_get(v_a_5472_, 0);
lean_inc(v_val_5480_);
lean_dec_ref_known(v_a_5472_, 1);
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 0, v_val_5480_);
v___x_5482_ = v___x_5474_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_val_5480_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
else
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5492_; 
lean_dec(v_a_5469_);
v_a_5485_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5487_ = v___x_5471_;
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5471_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5500_; 
v_a_5493_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5495_ = v___x_5468_;
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5468_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
if (v_isShared_5496_ == 0)
{
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object* v___x_5501_, lean_object* v___x_5502_, lean_object* v___x_5503_, lean_object* v___x_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_){
_start:
{
uint8_t v___x_6726__boxed_5514_; uint8_t v___x_6727__boxed_5515_; lean_object* v_res_5516_; 
v___x_6726__boxed_5514_ = lean_unbox(v___x_5503_);
v___x_6727__boxed_5515_ = lean_unbox(v___x_5504_);
v_res_5516_ = l_Lean_Elab_Tactic_evalRename___lam__0(v___x_5501_, v___x_5502_, v___x_6726__boxed_5514_, v___x_6727__boxed_5515_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
return v_res_5516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object* v___x_5517_, lean_object* v_h_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v___x_5528_; 
v___x_5528_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v___x_5517_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5528_) == 0)
{
lean_object* v_a_5529_; lean_object* v___x_5530_; 
v_a_5529_ = lean_ctor_get(v___x_5528_, 0);
lean_inc(v_a_5529_);
lean_dec_ref_known(v___x_5528_, 1);
v___x_5530_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5520_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_object* v_a_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
lean_inc(v_a_5531_);
lean_dec_ref_known(v___x_5530_, 1);
v___x_5532_ = l_Lean_TSyntax_getId(v_h_5518_);
v___x_5533_ = l_Lean_MVarId_rename(v_a_5531_, v_a_5529_, v___x_5532_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5533_, 1);
v___x_5535_ = lean_box(0);
v___x_5536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5536_, 0, v_a_5534_);
lean_ctor_set(v___x_5536_, 1, v___x_5535_);
v___x_5537_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5536_, v___y_5520_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
return v___x_5537_;
}
else
{
lean_object* v_a_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5545_; 
v_a_5538_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5540_ = v___x_5533_;
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_a_5538_);
lean_dec(v___x_5533_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
else
{
lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5553_; 
lean_dec(v_a_5529_);
v_a_5546_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5548_ = v___x_5530_;
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5530_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5551_; 
if (v_isShared_5549_ == 0)
{
v___x_5551_ = v___x_5548_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_a_5546_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
}
}
else
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5561_; 
v_a_5554_ = lean_ctor_get(v___x_5528_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5528_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5556_ = v___x_5528_;
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5528_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5559_; 
if (v_isShared_5557_ == 0)
{
v___x_5559_ = v___x_5556_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object* v___x_5562_, lean_object* v_h_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_){
_start:
{
lean_object* v_res_5573_; 
v_res_5573_ = l_Lean_Elab_Tactic_evalRename___lam__1(v___x_5562_, v_h_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
lean_dec(v_h_5563_);
return v_res_5573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* v_stx_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_){
_start:
{
lean_object* v___x_5593_; uint8_t v___x_5594_; 
v___x_5593_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
lean_inc(v_stx_5583_);
v___x_5594_ = l_Lean_Syntax_isOfKind(v_stx_5583_, v___x_5593_);
if (v___x_5594_ == 0)
{
lean_object* v___x_5595_; 
lean_dec(v_stx_5583_);
v___x_5595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_5595_;
}
else
{
lean_object* v___x_5596_; lean_object* v_h_5597_; lean_object* v___x_5598_; uint8_t v___x_5599_; 
v___x_5596_ = lean_unsigned_to_nat(3u);
v_h_5597_ = l_Lean_Syntax_getArg(v_stx_5583_, v___x_5596_);
v___x_5598_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__3));
lean_inc(v_h_5597_);
v___x_5599_ = l_Lean_Syntax_isOfKind(v_h_5597_, v___x_5598_);
if (v___x_5599_ == 0)
{
lean_object* v___x_5600_; 
lean_dec(v_h_5597_);
lean_dec(v_stx_5583_);
v___x_5600_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_5600_;
}
else
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___f_5606_; lean_object* v___x_5607_; uint8_t v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___f_5611_; lean_object* v___x_5612_; 
v___x_5601_ = lean_unsigned_to_nat(1u);
v___x_5602_ = l_Lean_Syntax_getArg(v_stx_5583_, v___x_5601_);
lean_dec(v_stx_5583_);
v___x_5603_ = lean_box(0);
v___x_5604_ = lean_box(v___x_5599_);
v___x_5605_ = lean_box(v___x_5594_);
v___f_5606_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__0___boxed), 13, 4);
lean_closure_set(v___f_5606_, 0, v___x_5602_);
lean_closure_set(v___f_5606_, 1, v___x_5603_);
lean_closure_set(v___f_5606_, 2, v___x_5604_);
lean_closure_set(v___f_5606_, 3, v___x_5605_);
v___x_5607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_5607_, 0, lean_box(0));
lean_closure_set(v___x_5607_, 1, v___f_5606_);
v___x_5608_ = 0;
v___x_5609_ = lean_box(v___x_5608_);
v___x_5610_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed), 12, 3);
lean_closure_set(v___x_5610_, 0, lean_box(0));
lean_closure_set(v___x_5610_, 1, v___x_5607_);
lean_closure_set(v___x_5610_, 2, v___x_5609_);
v___f_5611_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__1___boxed), 11, 2);
lean_closure_set(v___f_5611_, 0, v___x_5610_);
lean_closure_set(v___f_5611_, 1, v_h_5597_);
v___x_5612_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5611_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_);
return v___x_5612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object* v_stx_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_Lean_Elab_Tactic_evalRename(v_stx_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_);
lean_dec(v_a_5621_);
lean_dec_ref(v_a_5620_);
lean_dec(v_a_5619_);
lean_dec_ref(v_a_5618_);
lean_dec(v_a_5617_);
lean_dec_ref(v_a_5616_);
lean_dec(v_a_5615_);
lean_dec_ref(v_a_5614_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object* v_a_5624_, uint8_t v___x_5625_, lean_object* v_as_5626_, lean_object* v_i_5627_, lean_object* v_a_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
lean_object* v___x_5638_; 
v___x_5638_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_5624_, v___x_5625_, v_as_5626_, v_i_5627_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
return v___x_5638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object* v_a_5639_, lean_object* v___x_5640_, lean_object* v_as_5641_, lean_object* v_i_5642_, lean_object* v_a_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_){
_start:
{
uint8_t v___x_7000__boxed_5653_; lean_object* v_res_5654_; 
v___x_7000__boxed_5653_ = lean_unbox(v___x_5640_);
v_res_5654_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(v_a_5639_, v___x_7000__boxed_5653_, v_as_5641_, v_i_5642_, v_a_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_);
lean_dec(v___y_5651_);
lean_dec_ref(v___y_5650_);
lean_dec(v___y_5649_);
lean_dec_ref(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec_ref(v_as_5641_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object* v_a_5655_, uint8_t v___x_5656_, lean_object* v_as_5657_, lean_object* v_i_5658_, lean_object* v_a_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_5655_, v___x_5656_, v_as_5657_, v_i_5658_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_a_5670_, lean_object* v___x_5671_, lean_object* v_as_5672_, lean_object* v_i_5673_, lean_object* v_a_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_){
_start:
{
uint8_t v___x_7038__boxed_5684_; lean_object* v_res_5685_; 
v___x_7038__boxed_5684_ = lean_unbox(v___x_5671_);
v_res_5685_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(v_a_5670_, v___x_7038__boxed_5684_, v_as_5672_, v_i_5673_, v_a_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec(v___y_5676_);
lean_dec_ref(v___y_5675_);
lean_dec_ref(v_as_5672_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(){
_start:
{
lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; 
v___x_5693_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5694_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
v___x_5695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_5696_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___boxed), 10, 0);
v___x_5697_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5693_, v___x_5694_, v___x_5695_, v___x_5696_);
return v___x_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object* v_a_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(){
_start:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; 
v___x_5726_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_5727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6));
v___x_5728_ = l_Lean_addBuiltinDeclarationRanges(v___x_5726_, v___x_5727_);
return v___x_5728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object* v_a_5729_){
_start:
{
lean_object* v_res_5730_; 
v_res_5730_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
return v_res_5730_;
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
