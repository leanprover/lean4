// Lean compiler output
// Module: Lean.Elab.Tactic.Decide
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Meta.Tactic.Cleanup import Lean.Meta.Native import Lean.Elab.Tactic.ElabTerm import Lean.Elab.ConfigEval
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Expected type must not contain free variables"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "Use the `+revert` option to automatically clean up and revert free variables"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Expected type must not contain metavariables"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 237, 71, 156, 244, 3, 80, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 96, 18, 10, 225, 62, 78, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "` evaluated that the proposition"};
static const lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nis false"};
static const lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` failed to reduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\nto `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` or `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "`.\n\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_value),LEAN_SCALAR_PTR_LITERAL(76, 246, 154, 249, 193, 98, 251, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Reduction got stuck on `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, which indicates that a `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "` instance is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. The `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "` tactic works by evaluating a decision procedure via reduction, and it cannot make progress with such instances. This can occur due to the `open scoped Classical` command, which enables the instance `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "propDecidable"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value),LEAN_SCALAR_PTR_LITERAL(166, 239, 88, 215, 135, 192, 113, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 28, .m_data = "Reduction got stuck on `▸` ("};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "), which suggests that one of the `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "` instances is defined using tactics such as `rw` or `simp`. To avoid tactics, make use of functions such as `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value),LEAN_SCALAR_PTR_LITERAL(120, 135, 37, 233, 184, 173, 222, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "decidable_of_decidable_of_iff"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value),LEAN_SCALAR_PTR_LITERAL(191, 29, 120, 93, 238, 147, 138, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` to alter a proposition."};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "After unfolding the "};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = ", reduction got stuck at"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Reduction got stuck at"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` proved that the proposition"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` failed. The elaborator is able to reduce the `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` instance, but the kernel fails with:\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "` failed: Cannot simultaneously set both `+kernel` and `+native`"};
static const lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "DecideConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 154, 224, 188, 146, 89, 215, 198)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig;
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "kernel"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "native"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "revert"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "zetaReduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 154, 224, 188, 146, 89, 215, 198)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(180, 230, 247, 3, 189, 56, 137, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 154, 224, 188, 146, 89, 215, 198)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 91, 140, 101, 24, 220, 193, 39)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 154, 224, 188, 146, 89, 215, 198)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(106, 54, 19, 126, 23, 215, 136, 147)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 154, 224, 188, 146, 89, 215, 198)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(244, 203, 23, 23, 159, 112, 63, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(204, 31, 201, 122, 54, 242, 99, 241)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(373) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(397) << 1) | 1)),((lean_object*)(((size_t)(74) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value),((lean_object*)(((size_t)(74) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(373) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(373) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "native_decide"};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 101, 7, 237, 41, 103, 237, 127)}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 229, 81, 15, 25, 144, 49, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalNativeDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 133, 224, 42, 29, 33, 56, 192)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(410) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(417) << 1) | 1)),((lean_object*)(((size_t)(160) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value),((lean_object*)(((size_t)(160) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(410) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(410) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_e_30_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_box(1);
v___x_49_ = l_Lean_MessageData_ofFormat(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2));
v___x_54_ = l_Lean_MessageData_ofFormat(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4(lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
return v_x_55_;
}
else
{
lean_object* v_head_57_; lean_object* v_tail_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_80_; 
v_head_57_ = lean_ctor_get(v_x_56_, 0);
v_tail_58_ = lean_ctor_get(v_x_56_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_80_ == 0)
{
v___x_60_ = v_x_56_;
v_isShared_61_ = v_isSharedCheck_80_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_tail_58_);
lean_inc(v_head_57_);
lean_dec(v_x_56_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_80_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_before_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_78_; 
v_before_62_ = lean_ctor_get(v_head_57_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_head_57_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_head_57_, 1);
lean_dec(v_unused_79_);
v___x_64_ = v_head_57_;
v_isShared_65_ = v_isSharedCheck_78_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_before_62_);
lean_dec(v_head_57_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_78_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 7);
lean_ctor_set(v___x_64_, 1, v___x_66_);
lean_ctor_set(v___x_64_, 0, v_x_55_);
v___x_68_ = v___x_64_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_x_55_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_77_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 7);
lean_ctor_set(v___x_60_, 1, v___x_69_);
lean_ctor_set(v___x_60_, 0, v___x_68_);
v___x_71_ = v___x_60_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_69_);
v___x_71_ = v_reuseFailAlloc_76_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = l_Lean_MessageData_ofSyntax(v_before_62_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v___x_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_71_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v_x_55_ = v___x_74_;
v_x_56_ = v_tail_58_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(lean_object* v_opts_81_, lean_object* v_opt_82_){
_start:
{
lean_object* v_name_83_; lean_object* v_defValue_84_; lean_object* v_map_85_; lean_object* v___x_86_; 
v_name_83_ = lean_ctor_get(v_opt_82_, 0);
v_defValue_84_ = lean_ctor_get(v_opt_82_, 1);
v_map_85_ = lean_ctor_get(v_opts_81_, 0);
v___x_86_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_85_, v_name_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
uint8_t v___x_87_; 
v___x_87_ = lean_unbox(v_defValue_84_);
return v___x_87_;
}
else
{
lean_object* v_val_88_; 
v_val_88_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_val_88_);
lean_dec_ref_known(v___x_86_, 1);
if (lean_obj_tag(v_val_88_) == 1)
{
uint8_t v_v_89_; 
v_v_89_ = lean_ctor_get_uint8(v_val_88_, 0);
lean_dec_ref_known(v_val_88_, 0);
return v_v_89_;
}
else
{
uint8_t v___x_90_; 
lean_dec(v_val_88_);
v___x_90_ = lean_unbox(v_defValue_84_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_91_, lean_object* v_opt_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v_opts_91_, v_opt_92_);
lean_dec_ref(v_opt_92_);
lean_dec_ref(v_opts_91_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1));
v___x_99_ = l_Lean_MessageData_ofFormat(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(lean_object* v_msgData_100_, lean_object* v_macroStack_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_102_);
v___x_105_ = l_Lean_Elab_pp_macroStack;
v___x_106_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_104_, v___x_105_);
lean_dec_ref(v___x_104_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec(v_macroStack_101_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v_msgData_100_);
return v___x_107_;
}
else
{
if (lean_obj_tag(v_macroStack_101_) == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v_msgData_100_);
return v___x_108_;
}
else
{
lean_object* v_head_109_; lean_object* v_after_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_125_; 
v_head_109_ = lean_ctor_get(v_macroStack_101_, 0);
lean_inc(v_head_109_);
v_after_110_ = lean_ctor_get(v_head_109_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_head_109_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; 
v_unused_126_ = lean_ctor_get(v_head_109_, 0);
lean_dec(v_unused_126_);
v___x_112_ = v_head_109_;
v_isShared_113_ = v_isSharedCheck_125_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_after_110_);
lean_dec(v_head_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_125_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 7);
lean_ctor_set(v___x_112_, 1, v___x_114_);
lean_ctor_set(v___x_112_, 0, v_msgData_100_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_msgData_100_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_124_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_msgData_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_117_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2);
v___x_118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = l_Lean_MessageData_ofSyntax(v_after_110_);
v___x_120_ = l_Lean_indentD(v___x_119_);
v_msgData_121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_121_, 0, v___x_118_);
lean_ctor_set(v_msgData_121_, 1, v___x_120_);
v___x_122_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4(v_msgData_121_, v_macroStack_101_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_127_, lean_object* v_macroStack_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_127_, v_macroStack_128_, v___y_129_);
lean_dec_ref(v___y_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(lean_object* v_msgData_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_env_139_; uint8_t v___x_140_; lean_object* v_env_141_; lean_object* v___x_142_; lean_object* v_toCold_143_; lean_object* v_mctx_144_; lean_object* v_lctx_145_; lean_object* v_options_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v___x_140_ = 0;
v_env_141_ = l_Lean_Environment_setRecordingDeps(v_env_139_, v___x_140_);
v___x_142_ = lean_st_ref_get(v___y_134_);
v_toCold_143_ = lean_ctor_get(v___y_135_, 0);
v_mctx_144_ = lean_ctor_get(v___x_142_, 0);
lean_inc_ref(v_mctx_144_);
lean_dec(v___x_142_);
v_lctx_145_ = lean_ctor_get(v___y_133_, 2);
v_options_146_ = lean_ctor_get(v_toCold_143_, 2);
lean_inc_ref(v_options_146_);
lean_inc_ref(v_lctx_145_);
v___x_147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_147_, 0, v_env_141_);
lean_ctor_set(v___x_147_, 1, v_mctx_144_);
lean_ctor_set(v___x_147_, 2, v_lctx_145_);
lean_ctor_set(v___x_147_, 3, v_options_146_);
v___x_148_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_msgData_132_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0___boxed(lean_object* v_msgData_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msgData_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_ref_165_; lean_object* v_macroStack_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_ref_165_ = lean_ctor_get(v___y_162_, 2);
v_macroStack_166_ = lean_ctor_get(v___y_158_, 1);
v___x_167_ = l_Lean_Elab_getBetterRef(v_ref_165_, v_macroStack_166_);
v___x_168_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_157_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v___x_168_);
lean_inc(v_macroStack_166_);
v___x_170_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_a_169_, v_macroStack_166_, v___y_162_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_167_);
lean_ctor_set(v___x_175_, 1, v_a_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 1);
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg___boxed(lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_188_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0));
v___x_191_ = l_Lean_stringToMessageData(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3);
v___x_196_ = l_Lean_MessageData_hint_x27(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object* v_expectedType_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v_expectedType_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___x_253_; lean_object* v_a_254_; uint8_t v___x_255_; 
v___x_253_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_expectedType_200_, v_a_204_);
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref(v___x_253_);
v___x_255_ = l_Lean_Expr_hasFVar(v_a_254_);
if (v___x_255_ == 0)
{
v_expectedType_233_ = v_a_254_;
v___y_234_ = v_a_201_;
v___y_235_ = v_a_202_;
v___y_236_ = v_a_203_;
v___y_237_ = v_a_204_;
v___y_238_ = v_a_205_;
v___y_239_ = v_a_206_;
goto v___jp_232_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_zetaReduce(v_a_254_, v___x_255_, v___x_255_, v___x_255_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v_expectedType_233_ = v_a_257_;
v___y_234_ = v_a_201_;
v___y_235_ = v_a_202_;
v___y_236_ = v_a_203_;
v___y_237_ = v_a_204_;
v___y_238_ = v_a_205_;
v___y_239_ = v_a_206_;
goto v___jp_232_;
}
else
{
return v___x_256_;
}
}
v___jp_208_:
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Expr_hasFVar(v___y_209_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___y_209_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v___x_218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1);
v___x_219_ = l_Lean_indentExpr(v___y_209_);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_222_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
v___jp_232_:
{
uint8_t v___x_240_; 
v___x_240_ = l_Lean_Expr_hasMVar(v_expectedType_233_);
if (v___x_240_ == 0)
{
v___y_209_ = v_expectedType_233_;
v___y_210_ = v___y_234_;
v___y_211_ = v___y_235_;
v___y_212_ = v___y_236_;
v___y_213_ = v___y_237_;
v___y_214_ = v___y_238_;
v___y_215_ = v___y_239_;
goto v___jp_208_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v___x_241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6);
v___x_242_ = l_Lean_indentExpr(v_expectedType_233_);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_243_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(lean_object* v_expectedType_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(lean_object* v_00_u03b1_267_, lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___boxed(lean_object* v_00_u03b1_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(v_00_u03b1_277_, v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(lean_object* v_msgData_287_, lean_object* v_macroStack_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_287_, v_macroStack_288_, v___y_293_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___boxed(lean_object* v_msgData_297_, lean_object* v_macroStack_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(v_msgData_297_, v_macroStack_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(lean_object* v_declName_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_env_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_st_ref_get(v___y_308_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_env_311_);
lean_dec(v___x_310_);
v___x_312_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_311_, v_declName_307_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(lean_object* v_declName_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_314_, v___y_315_);
lean_dec(v___y_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(lean_object* v_declName_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_318_, v___y_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(lean_object* v_declName_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(v_declName_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_331_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Lean_maxRecDepthErrorMessage;
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3);
v___x_340_ = l_Lean_MessageData_ofFormat(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4);
v___x_342_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_343_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object* v_ref_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_ref_344_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object* v_ref_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object* v_00_u03b1_352_, lean_object* v_ref_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_353_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object* v_00_u03b1_360_, lean_object* v_ref_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(v_00_u03b1_360_, v_ref_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0(void){
_start:
{
lean_object* v___x_385_; lean_object* v_dummy_386_; 
v___x_385_ = lean_box(0);
v_dummy_386_ = l_Lean_Expr_sort___override(v___x_385_);
return v_dummy_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* v_expr_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v_toCold_498_; lean_object* v_currRecDepth_499_; lean_object* v_ref_500_; uint16_t v_optionFlags_501_; uint8_t v_suppressElabErrors_502_; uint8_t v_checkDeprecated_503_; uint8_t v_isRecordingDeps_504_; lean_object* v_maxRecDepth_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_toCold_498_ = lean_ctor_get(v_a_401_, 0);
lean_inc_ref(v_toCold_498_);
v_currRecDepth_499_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_currRecDepth_499_);
v_ref_500_ = lean_ctor_get(v_a_401_, 2);
lean_inc(v_ref_500_);
v_optionFlags_501_ = lean_ctor_get_uint16(v_a_401_, sizeof(void*)*3);
v_suppressElabErrors_502_ = lean_ctor_get_uint8(v_a_401_, sizeof(void*)*3 + 2);
v_checkDeprecated_503_ = lean_ctor_get_uint8(v_a_401_, sizeof(void*)*3 + 3);
v_isRecordingDeps_504_ = lean_ctor_get_uint8(v_a_401_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_401_);
v_maxRecDepth_518_ = lean_ctor_get(v_toCold_498_, 3);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_nat_dec_eq(v_maxRecDepth_518_, v___x_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_eq(v_currRecDepth_499_, v_maxRecDepth_518_);
if (v___x_521_ == 0)
{
goto v___jp_505_;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_currRecDepth_499_);
lean_dec_ref(v_toCold_498_);
lean_dec_ref(v_expr_398_);
v___x_522_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_500_);
return v___x_522_;
}
}
else
{
goto v___jp_505_;
}
v___jp_404_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(3u);
v___x_410_ = lean_nat_sub(v___y_406_, v___x_409_);
lean_dec(v___y_406_);
v___x_411_ = lean_nat_sub(v___x_410_, v___y_407_);
lean_dec(v___x_410_);
v___x_412_ = l_Lean_Expr_getRevArg_x21(v___y_405_, v___x_411_);
lean_dec_ref(v___y_405_);
v_expr_398_ = v___x_412_;
v_a_401_ = v___y_408_;
goto _start;
}
v___jp_414_:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Expr_getAppFn(v___y_416_);
if (lean_obj_tag(v___x_422_) == 4)
{
lean_object* v_declName_423_; lean_object* v___x_424_; 
v_declName_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_declName_423_);
lean_dec_ref_known(v___x_422_, 2);
v___x_424_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_423_, v___y_421_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_467_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_467_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_467_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_467_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
if (lean_obj_tag(v_a_425_) == 1)
{
lean_object* v_val_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_val_429_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_val_429_);
lean_dec_ref_known(v_a_425_, 1);
v___x_430_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_429_);
v___x_431_ = lean_nat_dec_le(v___x_430_, v___y_415_);
lean_dec(v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v_val_429_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_415_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___y_416_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___y_416_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_object* v_numDiscrs_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_dummy_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_del_object(v___x_427_);
v_numDiscrs_435_ = lean_ctor_get(v_val_429_, 1);
lean_inc(v_numDiscrs_435_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1));
v_dummy_438_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0);
lean_inc(v___y_415_);
v___x_439_ = lean_mk_array(v___y_415_, v_dummy_438_);
v___x_440_ = lean_nat_sub(v___y_415_, v___y_417_);
lean_dec(v___y_415_);
lean_inc_ref(v___y_416_);
v___x_441_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_416_, v___x_439_, v___x_440_);
v___x_442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_numDiscrs_435_, v_val_429_, v___x_441_, v___x_436_, v___x_437_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v___x_441_);
lean_dec(v_val_429_);
lean_dec(v_numDiscrs_435_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_455_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_455_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_fst_447_; 
v_fst_447_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_fst_447_);
lean_dec(v_a_443_);
if (lean_obj_tag(v_fst_447_) == 0)
{
lean_object* v___x_449_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___y_416_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___y_416_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v_val_451_; lean_object* v___x_453_; 
lean_dec_ref(v___y_416_);
v_val_451_ = lean_ctor_get(v_fst_447_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v_fst_447_, 1);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_val_451_);
v___x_453_ = v___x_445_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_val_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v___y_416_);
v_a_456_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_442_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_442_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
else
{
lean_object* v___x_465_; 
lean_dec(v_a_425_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_415_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___y_416_);
v___x_465_ = v___x_427_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___y_416_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v___y_420_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
v_a_468_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_424_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_424_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_476_; 
lean_dec_ref(v___x_422_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_415_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___y_416_);
return v___x_476_;
}
}
v___jp_477_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_482_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0));
v___x_483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2));
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = l_Lean_Expr_isAppOfArity(v___y_478_, v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
if (lean_obj_tag(v___y_478_) == 11)
{
lean_object* v_typeName_486_; 
v_typeName_486_ = lean_ctor_get(v___y_478_, 0);
if (lean_obj_tag(v_typeName_486_) == 1)
{
lean_object* v_pre_487_; 
v_pre_487_ = lean_ctor_get(v_typeName_486_, 0);
if (lean_obj_tag(v_pre_487_) == 0)
{
lean_object* v_idx_488_; lean_object* v_struct_489_; lean_object* v_str_490_; uint8_t v___x_491_; 
v_idx_488_ = lean_ctor_get(v___y_478_, 1);
v_struct_489_ = lean_ctor_get(v___y_478_, 2);
v_str_490_ = lean_ctor_get(v_typeName_486_, 1);
v___x_491_ = lean_string_dec_eq(v_str_490_, v___x_482_);
if (v___x_491_ == 0)
{
v___y_415_ = v___y_479_;
v___y_416_ = v___y_478_;
v___y_417_ = v___y_480_;
v___y_418_ = v_a_399_;
v___y_419_ = v_a_400_;
v___y_420_ = v___y_481_;
v___y_421_ = v_a_402_;
goto v___jp_414_;
}
else
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_nat_dec_eq(v_idx_488_, v___x_492_);
if (v___x_493_ == 0)
{
v___y_415_ = v___y_479_;
v___y_416_ = v___y_478_;
v___y_417_ = v___y_480_;
v___y_418_ = v_a_399_;
v___y_419_ = v_a_400_;
v___y_420_ = v___y_481_;
v___y_421_ = v_a_402_;
goto v___jp_414_;
}
else
{
lean_inc_ref(v_struct_489_);
lean_dec_ref_known(v___y_478_, 3);
lean_dec(v___y_479_);
v_expr_398_ = v_struct_489_;
v_a_401_ = v___y_481_;
goto _start;
}
}
}
else
{
v___y_415_ = v___y_479_;
v___y_416_ = v___y_478_;
v___y_417_ = v___y_480_;
v___y_418_ = v_a_399_;
v___y_419_ = v_a_400_;
v___y_420_ = v___y_481_;
v___y_421_ = v_a_402_;
goto v___jp_414_;
}
}
else
{
v___y_415_ = v___y_479_;
v___y_416_ = v___y_478_;
v___y_417_ = v___y_480_;
v___y_418_ = v_a_399_;
v___y_419_ = v_a_400_;
v___y_420_ = v___y_481_;
v___y_421_ = v_a_402_;
goto v___jp_414_;
}
}
else
{
v___y_415_ = v___y_479_;
v___y_416_ = v___y_478_;
v___y_417_ = v___y_480_;
v___y_418_ = v_a_399_;
v___y_419_ = v_a_400_;
v___y_420_ = v___y_481_;
v___y_421_ = v_a_402_;
goto v___jp_414_;
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v___y_479_);
v___x_495_ = l_Lean_Expr_appFn_x21(v___y_478_);
lean_dec_ref(v___y_478_);
v___x_496_ = l_Lean_Expr_appArg_x21(v___x_495_);
lean_dec_ref(v___x_495_);
v_expr_398_ = v___x_496_;
v_a_401_ = v___y_481_;
goto _start;
}
}
v___jp_505_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_currRecDepth_499_, v___x_506_);
lean_dec(v_currRecDepth_499_);
v___x_508_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_508_, 0, v_toCold_498_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
lean_ctor_set(v___x_508_, 2, v_ref_500_);
lean_ctor_set_uint16(v___x_508_, sizeof(void*)*3, v_optionFlags_501_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*3 + 2, v_suppressElabErrors_502_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*3 + 3, v_checkDeprecated_503_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*3 + 4, v_isRecordingDeps_504_);
lean_inc(v_a_402_);
lean_inc_ref(v___x_508_);
lean_inc(v_a_400_);
lean_inc_ref(v_a_399_);
v___x_509_ = lean_whnf(v_expr_398_, v_a_399_, v_a_400_, v___x_508_, v_a_402_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Expr_getAppNumArgs(v_a_510_);
v___x_512_ = lean_unsigned_to_nat(4u);
v___x_513_ = lean_nat_dec_le(v___x_512_, v___x_511_);
if (v___x_513_ == 0)
{
v___y_478_ = v_a_510_;
v___y_479_ = v___x_511_;
v___y_480_ = v___x_506_;
v___y_481_ = v___x_508_;
goto v___jp_477_;
}
else
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4));
v___x_515_ = l_Lean_Expr_isAppOf(v_a_510_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5));
v___x_517_ = l_Lean_Expr_isAppOf(v_a_510_, v___x_516_);
if (v___x_517_ == 0)
{
v___y_478_ = v_a_510_;
v___y_479_ = v___x_511_;
v___y_480_ = v___x_506_;
v___y_481_ = v___x_508_;
goto v___jp_477_;
}
else
{
v___y_405_ = v_a_510_;
v___y_406_ = v___x_511_;
v___y_407_ = v___x_506_;
v___y_408_ = v___x_508_;
goto v___jp_404_;
}
}
else
{
v___y_405_ = v_a_510_;
v___y_406_ = v___x_511_;
v___y_407_ = v___x_506_;
v___y_408_ = v___x_508_;
goto v___jp_404_;
}
}
}
else
{
lean_dec_ref_known(v___x_508_, 3);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(lean_object* v_upperBound_523_, lean_object* v_val_524_, lean_object* v___x_525_, lean_object* v_a_526_, lean_object* v_b_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_a_534_; uint8_t v___x_538_; 
v___x_538_ = lean_nat_dec_lt(v_a_526_, v_upperBound_523_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v_a_526_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_b_527_);
return v___x_539_;
}
else
{
lean_object* v_numParams_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_b_527_);
v_numParams_540_ = lean_ctor_get(v_val_524_, 0);
v___x_541_ = l_Lean_instInhabitedExpr;
v___x_542_ = lean_box(0);
v___x_543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1));
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v_numParams_540_, v___x_544_);
v___x_546_ = lean_nat_add(v___x_545_, v_a_526_);
lean_dec(v___x_545_);
v___x_547_ = lean_array_get_borrowed(v___x_541_, v___x_525_, v___x_546_);
lean_dec(v___x_546_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc(v___x_547_);
v___x_548_ = lean_infer_type(v___x_547_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
v___x_550_ = lean_whnf(v_a_549_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3));
v___x_553_ = l_Lean_Expr_isConstOf(v_a_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4));
v___x_555_ = l_Lean_Expr_isAppOf(v_a_551_, v___x_554_);
lean_dec(v_a_551_);
if (v___x_555_ == 0)
{
v_a_534_ = v___x_543_;
goto v___jp_533_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_547_);
v___x_557_ = l_Lean_Expr_proj___override(v___x_554_, v___x_556_, v___x_547_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
v___x_558_ = lean_whnf(v___x_557_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_561_ = l_Lean_Expr_isConstOf(v_a_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_563_ = l_Lean_Expr_isConstOf(v_a_559_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v_a_526_);
lean_inc_ref(v___y_530_);
v___x_564_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_559_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_574_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v_a_565_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_542_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_a_575_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_564_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_564_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_dec(v_a_559_);
v_a_534_ = v___x_543_;
goto v___jp_533_;
}
}
else
{
lean_dec(v_a_559_);
v_a_534_ = v___x_543_;
goto v___jp_533_;
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_a_526_);
v_a_583_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_558_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_558_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec(v_a_551_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc(v___x_547_);
v___x_591_ = lean_whnf(v___x_547_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_594_ = l_Lean_Expr_isConstOf(v_a_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_596_ = l_Lean_Expr_isConstOf(v_a_592_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec(v_a_526_);
lean_inc_ref(v___y_530_);
v___x_597_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_592_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_a_598_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_542_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_605_ = v___x_600_;
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
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_597_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_597_);
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
lean_dec(v_a_592_);
v_a_534_ = v___x_543_;
goto v___jp_533_;
}
}
else
{
lean_dec(v_a_592_);
v_a_534_ = v___x_543_;
goto v___jp_533_;
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_526_);
v_a_616_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_591_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_591_);
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
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_a_526_);
v_a_624_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_550_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_550_);
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
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_a_526_);
v_a_632_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_548_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_548_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_a_526_, v___x_535_);
lean_dec(v_a_526_);
lean_inc_ref(v_a_534_);
v_a_526_ = v___x_536_;
v_b_527_ = v_a_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___boxed(lean_object* v_upperBound_640_, lean_object* v_val_641_, lean_object* v___x_642_, lean_object* v_a_643_, lean_object* v_b_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_upperBound_640_, v_val_641_, v___x_642_, v_a_643_, v_b_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___x_642_);
lean_dec_ref(v_val_641_);
lean_dec(v_upperBound_640_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object* v_expr_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_expr_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(lean_object* v_upperBound_658_, lean_object* v_val_659_, lean_object* v___x_660_, lean_object* v_inst_661_, lean_object* v_R_662_, lean_object* v_a_663_, lean_object* v_b_664_, lean_object* v_c_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_upperBound_658_, v_val_659_, v___x_660_, v_a_663_, v_b_664_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(lean_object* v_upperBound_672_, lean_object* v_val_673_, lean_object* v___x_674_, lean_object* v_inst_675_, lean_object* v_R_676_, lean_object* v_a_677_, lean_object* v_b_678_, lean_object* v_c_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_upperBound_672_, v_val_673_, v___x_674_, v_inst_675_, v_R_676_, v_a_677_, v_b_678_, v_c_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v___x_674_);
lean_dec_ref(v_val_673_);
lean_dec(v_upperBound_672_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_ref_692_; lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_ref_692_ = lean_ctor_get(v___y_689_, 2);
v___x_693_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
lean_inc(v_ref_692_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_ref_692_);
lean_ctor_set(v___x_698_, 1, v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 1);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1));
v___x_715_ = l_Lean_mkConst(v___x_714_, v___x_713_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3));
v___x_718_ = l_Lean_stringToMessageData(v___x_717_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5));
v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore(lean_object* v_tacticName_725_, lean_object* v_expectedType_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; 
lean_inc_ref(v_expectedType_726_);
v___x_736_ = l_Lean_Meta_mkDecide(v_expectedType_726_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_776_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_776_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_776_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_776_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_ref_741_; lean_object* v___x_743_; 
v_ref_741_ = lean_ctor_get(v_a_733_, 2);
lean_inc(v_ref_741_);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 1);
lean_ctor_set(v___x_739_, 0, v_ref_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_ref_741_);
v___x_743_ = v_reuseFailAlloc_775_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; 
lean_inc(v_a_737_);
lean_inc(v_tacticName_725_);
v___x_744_ = l_Lean_Meta_nativeEqTrue(v_tacticName_725_, v_a_737_, v___x_743_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec_ref(v___x_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_766_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_766_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
if (lean_obj_tag(v_a_745_) == 0)
{
lean_object* v_prf_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_tacticName_725_);
v_prf_749_ = lean_ctor_get(v_a_745_, 0);
lean_inc_ref(v_prf_749_);
lean_dec_ref_known(v_a_745_, 1);
v___x_750_ = l_Lean_Expr_appArg_x21(v_a_737_);
lean_dec(v_a_737_);
v___x_751_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_752_ = l_Lean_mkApp3(v___x_751_, v_expectedType_726_, v___x_750_, v_prf_749_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_752_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_del_object(v___x_747_);
lean_dec(v_a_737_);
v___x_756_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_757_ = l_Lean_MessageData_ofName(v_tacticName_725_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_indentExpr(v_expectedType_726_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_764_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_765_;
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_a_737_);
lean_dec_ref(v_expectedType_726_);
lean_dec(v_tacticName_725_);
v_a_767_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_744_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_744_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_726_);
lean_dec(v_tacticName_725_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(lean_object* v_tacticName_777_, lean_object* v_expectedType_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_777_, v_expectedType_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(lean_object* v_00_u03b1_789_, lean_object* v_msg_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_790_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(lean_object* v_00_u03b1_801_, lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(v_00_u03b1_801_, v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_812_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
if (lean_obj_tag(v_x_814_) == 0)
{
uint8_t v___x_815_; 
v___x_815_ = 1;
return v___x_815_;
}
else
{
uint8_t v___x_816_; 
v___x_816_ = 0;
return v___x_816_;
}
}
else
{
if (lean_obj_tag(v_x_814_) == 0)
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
else
{
lean_object* v_val_818_; lean_object* v_val_819_; uint8_t v___x_820_; 
v_val_818_ = lean_ctor_get(v_x_813_, 0);
v_val_819_ = lean_ctor_get(v_x_814_, 0);
v___x_820_ = lean_name_eq(v_val_818_, v_val_819_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_x_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec(v_x_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object* v_opts_825_, lean_object* v_opt_826_){
_start:
{
lean_object* v_name_827_; lean_object* v_defValue_828_; lean_object* v_map_829_; lean_object* v___x_830_; 
v_name_827_ = lean_ctor_get(v_opt_826_, 0);
v_defValue_828_ = lean_ctor_get(v_opt_826_, 1);
v_map_829_ = lean_ctor_get(v_opts_825_, 0);
v___x_830_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_829_, v_name_827_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_inc(v_defValue_828_);
return v_defValue_828_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_830_, 1);
if (lean_obj_tag(v_val_831_) == 3)
{
lean_object* v_v_832_; 
v_v_832_ = lean_ctor_get(v_val_831_, 0);
lean_inc(v_v_832_);
lean_dec_ref_known(v_val_831_, 1);
return v_v_832_;
}
else
{
lean_dec(v_val_831_);
lean_inc(v_defValue_828_);
return v_defValue_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object* v_opts_833_, lean_object* v_opt_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_opts_833_, v_opt_834_);
lean_dec_ref(v_opt_834_);
lean_dec_ref(v_opts_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Meta_saveState___redArg(v___y_838_, v___y_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v_r_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v_r_844_ = lean_apply_5(v_x_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
if (lean_obj_tag(v_r_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_845_ = lean_ctor_get(v_r_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v_r_844_, 1);
v___x_846_ = l_Lean_Meta_SavedState_restore___redArg(v_a_843_, v___y_838_, v___y_840_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_846_, 0);
lean_dec(v_unused_854_);
v___x_848_ = v___x_846_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_dec(v___x_846_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_a_845_);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_845_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_845_);
v_a_855_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_846_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_846_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_ctor_get(v_r_844_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v_r_844_, 1);
v___x_864_ = l_Lean_Meta_SavedState_restore___redArg(v_a_843_, v___y_838_, v___y_840_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_872_);
v___x_866_ = v___x_864_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_dec(v___x_864_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 1);
lean_ctor_set(v___x_866_, 0, v_a_863_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_863_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_863_);
v_a_873_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_864_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_864_);
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
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_x_836_);
v_a_881_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_842_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_842_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg___boxed(lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(lean_object* v_00_u03b1_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v_x_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___boxed(lean_object* v_00_u03b1_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(v_00_u03b1_904_, v_x_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object* v_cs_912_, lean_object* v_n_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_array_push(v_cs_912_, v_n_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object* v_cs_916_, lean_object* v_n_917_, lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(v_cs_916_, v_n_917_, v_x_918_);
lean_dec(v_x_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(lean_object* v_o_923_, lean_object* v_k_924_, uint8_t v_v_925_){
_start:
{
lean_object* v_map_926_; uint8_t v_hasTrace_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_941_; 
v_map_926_ = lean_ctor_get(v_o_923_, 0);
v_hasTrace_927_ = lean_ctor_get_uint8(v_o_923_, sizeof(void*)*1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_o_923_);
if (v_isSharedCheck_941_ == 0)
{
v___x_929_ = v_o_923_;
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_map_926_);
lean_dec(v_o_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_931_, 0, v_v_925_);
lean_inc(v_k_924_);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_924_, v___x_931_, v_map_926_);
if (v_hasTrace_927_ == 0)
{
lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_936_; 
v___x_933_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___closed__1));
v___x_934_ = l_Lean_Name_isPrefixOf(v___x_933_, v_k_924_);
lean_dec(v_k_924_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_936_ = v___x_929_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_932_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*1, v___x_934_);
return v___x_936_;
}
}
else
{
lean_object* v___x_939_; 
lean_dec(v_k_924_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_939_ = v___x_929_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*1, v_hasTrace_927_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___boxed(lean_object* v_o_942_, lean_object* v_k_943_, lean_object* v_v_944_){
_start:
{
uint8_t v_v_boxed_945_; lean_object* v_res_946_; 
v_v_boxed_945_ = lean_unbox(v_v_944_);
v_res_946_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(v_o_942_, v_k_943_, v_v_boxed_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object* v_opts_947_, lean_object* v_opt_948_, uint8_t v_val_949_){
_start:
{
lean_object* v_name_950_; lean_object* v___x_951_; 
v_name_950_ = lean_ctor_get(v_opt_948_, 0);
lean_inc(v_name_950_);
lean_dec_ref(v_opt_948_);
v___x_951_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(v_opts_947_, v_name_950_, v_val_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object* v_opts_952_, lean_object* v_opt_953_, lean_object* v_val_954_){
_start:
{
uint8_t v_val_boxed_955_; lean_object* v_res_956_; 
v_val_boxed_955_ = lean_unbox(v_val_954_);
v_res_956_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_opts_952_, v_opt_953_, v_val_boxed_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0(lean_object* v_f_957_, lean_object* v_x1_958_, lean_object* v_x2_959_, lean_object* v_x3_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_apply_3(v_f_957_, v_x1_958_, v_x2_959_, v_x3_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg(lean_object* v_f_962_, lean_object* v_keys_963_, lean_object* v_vals_964_, lean_object* v_i_965_, lean_object* v_acc_966_){
_start:
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_array_get_size(v_keys_963_);
v___x_968_ = lean_nat_dec_lt(v_i_965_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v_i_965_);
lean_dec(v_f_962_);
return v_acc_966_;
}
else
{
lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_k_969_ = lean_array_fget_borrowed(v_keys_963_, v_i_965_);
v_v_970_ = lean_array_fget_borrowed(v_vals_964_, v_i_965_);
lean_inc(v_f_962_);
lean_inc(v_v_970_);
lean_inc(v_k_969_);
v___x_971_ = lean_apply_3(v_f_962_, v_acc_966_, v_k_969_, v_v_970_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_i_965_, v___x_972_);
lean_dec(v_i_965_);
v_i_965_ = v___x_973_;
v_acc_966_ = v___x_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg___boxed(lean_object* v_f_975_, lean_object* v_keys_976_, lean_object* v_vals_977_, lean_object* v_i_978_, lean_object* v_acc_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg(v_f_975_, v_keys_976_, v_vals_977_, v_i_978_, v_acc_979_);
lean_dec_ref(v_vals_977_);
lean_dec_ref(v_keys_976_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_f_981_, lean_object* v_as_982_, size_t v_i_983_, size_t v_stop_984_, lean_object* v_b_985_){
_start:
{
lean_object* v___y_987_; uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_eq(v_i_983_, v_stop_984_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_array_uget_borrowed(v_as_982_, v_i_983_);
switch(lean_obj_tag(v___x_992_))
{
case 0:
{
lean_object* v_key_993_; lean_object* v_val_994_; lean_object* v___x_995_; 
v_key_993_ = lean_ctor_get(v___x_992_, 0);
v_val_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_f_981_);
lean_inc(v_val_994_);
lean_inc(v_key_993_);
v___x_995_ = lean_apply_3(v_f_981_, v_b_985_, v_key_993_, v_val_994_);
v___y_987_ = v___x_995_;
goto v___jp_986_;
}
case 1:
{
lean_object* v_node_996_; lean_object* v___x_997_; 
v_node_996_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_f_981_);
v___x_997_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(v_f_981_, v_node_996_, v_b_985_);
v___y_987_ = v___x_997_;
goto v___jp_986_;
}
default: 
{
v___y_987_ = v_b_985_;
goto v___jp_986_;
}
}
}
else
{
lean_dec(v_f_981_);
return v_b_985_;
}
v___jp_986_:
{
size_t v___x_988_; size_t v___x_989_; 
v___x_988_ = ((size_t)1ULL);
v___x_989_ = lean_usize_add(v_i_983_, v___x_988_);
v_i_983_ = v___x_989_;
v_b_985_ = v___y_987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(lean_object* v_f_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v_es_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_es_1001_ = lean_ctor_get(v_x_999_, 0);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_size(v_es_1001_);
v___x_1004_ = lean_nat_dec_lt(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec(v_f_998_);
return v_x_1000_;
}
else
{
size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = lean_usize_of_nat(v___x_1003_);
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg(v_f_998_, v_es_1001_, v___x_1005_, v___x_1006_, v_x_1000_);
return v___x_1007_;
}
}
else
{
lean_object* v_ks_1008_; lean_object* v_vs_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_ks_1008_ = lean_ctor_get(v_x_999_, 0);
v_vs_1009_ = lean_ctor_get(v_x_999_, 1);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg(v_f_998_, v_ks_1008_, v_vs_1009_, v___x_1010_, v_x_1000_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(v_f_1012_, v_x_1013_, v_x_1014_);
lean_dec_ref(v_x_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_f_1016_, lean_object* v_as_1017_, lean_object* v_i_1018_, lean_object* v_stop_1019_, lean_object* v_b_1020_){
_start:
{
size_t v_i_boxed_1021_; size_t v_stop_boxed_1022_; lean_object* v_res_1023_; 
v_i_boxed_1021_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_stop_boxed_1022_ = lean_unbox_usize(v_stop_1019_);
lean_dec(v_stop_1019_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg(v_f_1016_, v_as_1017_, v_i_boxed_1021_, v_stop_boxed_1022_, v_b_1020_);
lean_dec_ref(v_as_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(lean_object* v_map_1024_, lean_object* v_f_1025_, lean_object* v_init_1026_){
_start:
{
lean_object* v___f_1027_; lean_object* v___x_1028_; 
v___f_1027_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1027_, 0, v_f_1025_);
v___x_1028_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(v___f_1027_, v_map_1024_, v_init_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___boxed(lean_object* v_map_1029_, lean_object* v_f_1030_, lean_object* v_init_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_1029_, v_f_1030_, v_init_1031_);
lean_dec_ref(v_map_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg(lean_object* v_hi_1033_, lean_object* v_pivot_1034_, lean_object* v_as_1035_, lean_object* v_i_1036_, lean_object* v_k_1037_){
_start:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_lt(v_k_1037_, v_hi_1033_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v_k_1037_);
v___x_1039_ = lean_array_fswap(v_as_1035_, v_i_1036_, v_hi_1033_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_i_1036_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_array_fget_borrowed(v_as_1035_, v_k_1037_);
v___x_1042_ = l_Lean_Name_lt(v___x_1041_, v_pivot_1034_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_k_1037_, v___x_1043_);
lean_dec(v_k_1037_);
v_k_1037_ = v___x_1044_;
goto _start;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_array_fswap(v_as_1035_, v_i_1036_, v_k_1037_);
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_nat_add(v_i_1036_, v___x_1047_);
lean_dec(v_i_1036_);
v___x_1049_ = lean_nat_add(v_k_1037_, v___x_1047_);
lean_dec(v_k_1037_);
v_as_1035_ = v___x_1046_;
v_i_1036_ = v___x_1048_;
v_k_1037_ = v___x_1049_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg___boxed(lean_object* v_hi_1051_, lean_object* v_pivot_1052_, lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg(v_hi_1051_, v_pivot_1052_, v_as_1053_, v_i_1054_, v_k_1055_);
lean_dec(v_pivot_1052_);
lean_dec(v_hi_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(lean_object* v_n_1057_, lean_object* v_as_1058_, lean_object* v_lo_1059_, lean_object* v_hi_1060_){
_start:
{
lean_object* v___y_1062_; uint8_t v___x_1072_; 
v___x_1072_ = lean_nat_dec_lt(v_lo_1059_, v_hi_1060_);
if (v___x_1072_ == 0)
{
lean_dec(v_lo_1059_);
return v_as_1058_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_mid_1075_; lean_object* v___y_1077_; lean_object* v___y_1083_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1073_ = lean_nat_add(v_lo_1059_, v_hi_1060_);
v___x_1074_ = lean_unsigned_to_nat(1u);
v_mid_1075_ = lean_nat_shiftr(v___x_1073_, v___x_1074_);
lean_dec(v___x_1073_);
v___x_1088_ = lean_array_fget_borrowed(v_as_1058_, v_mid_1075_);
v___x_1089_ = lean_array_fget_borrowed(v_as_1058_, v_lo_1059_);
v___x_1090_ = l_Lean_Name_lt(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
v___y_1083_ = v_as_1058_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_array_fswap(v_as_1058_, v_lo_1059_, v_mid_1075_);
v___y_1083_ = v___x_1091_;
goto v___jp_1082_;
}
v___jp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = lean_array_fget_borrowed(v___y_1077_, v_mid_1075_);
v___x_1079_ = lean_array_fget_borrowed(v___y_1077_, v_hi_1060_);
v___x_1080_ = l_Lean_Name_lt(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec(v_mid_1075_);
v___y_1062_ = v___y_1077_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_array_fswap(v___y_1077_, v_mid_1075_, v_hi_1060_);
lean_dec(v_mid_1075_);
v___y_1062_ = v___x_1081_;
goto v___jp_1061_;
}
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_array_fget_borrowed(v___y_1083_, v_hi_1060_);
v___x_1085_ = lean_array_fget_borrowed(v___y_1083_, v_lo_1059_);
v___x_1086_ = l_Lean_Name_lt(v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
v___y_1077_ = v___y_1083_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_array_fswap(v___y_1083_, v_lo_1059_, v_hi_1060_);
v___y_1077_ = v___x_1087_;
goto v___jp_1076_;
}
}
}
v___jp_1061_:
{
lean_object* v_pivot_1063_; lean_object* v___x_1064_; lean_object* v_fst_1065_; lean_object* v_snd_1066_; uint8_t v___x_1067_; 
v_pivot_1063_ = lean_array_fget(v___y_1062_, v_hi_1060_);
lean_inc_n(v_lo_1059_, 2);
v___x_1064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg(v_hi_1060_, v_pivot_1063_, v___y_1062_, v_lo_1059_, v_lo_1059_);
lean_dec(v_pivot_1063_);
v_fst_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_fst_1065_);
v_snd_1066_ = lean_ctor_get(v___x_1064_, 1);
lean_inc(v_snd_1066_);
lean_dec_ref(v___x_1064_);
v___x_1067_ = lean_nat_dec_le(v_hi_1060_, v_fst_1065_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_1057_, v_snd_1066_, v_lo_1059_, v_fst_1065_);
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_add(v_fst_1065_, v___x_1069_);
lean_dec(v_fst_1065_);
v_as_1058_ = v___x_1068_;
v_lo_1059_ = v___x_1070_;
goto _start;
}
else
{
lean_dec(v_fst_1065_);
lean_dec(v_lo_1059_);
return v_snd_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(lean_object* v_n_1092_, lean_object* v_as_1093_, lean_object* v_lo_1094_, lean_object* v_hi_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_1092_, v_as_1093_, v_lo_1094_, v_hi_1095_);
lean_dec(v_hi_1095_);
lean_dec(v_n_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(lean_object* v_msg_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_ref_1103_; lean_object* v___x_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_ref_1103_ = lean_ctor_get(v___y_1100_, 2);
v___x_1104_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_inc(v_ref_1103_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_ref_1103_);
lean_ctor_set(v___x_1109_, 1, v_a_1105_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 1);
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg___boxed(lean_object* v_msg_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(lean_object* v_ref_1121_, lean_object* v_msg_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_toCold_1128_; lean_object* v_currRecDepth_1129_; lean_object* v_ref_1130_; uint16_t v_optionFlags_1131_; uint8_t v_suppressElabErrors_1132_; uint8_t v_checkDeprecated_1133_; uint8_t v_isRecordingDeps_1134_; lean_object* v_ref_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_toCold_1128_ = lean_ctor_get(v___y_1125_, 0);
v_currRecDepth_1129_ = lean_ctor_get(v___y_1125_, 1);
v_ref_1130_ = lean_ctor_get(v___y_1125_, 2);
v_optionFlags_1131_ = lean_ctor_get_uint16(v___y_1125_, sizeof(void*)*3);
v_suppressElabErrors_1132_ = lean_ctor_get_uint8(v___y_1125_, sizeof(void*)*3 + 2);
v_checkDeprecated_1133_ = lean_ctor_get_uint8(v___y_1125_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1134_ = lean_ctor_get_uint8(v___y_1125_, sizeof(void*)*3 + 4);
v_ref_1135_ = l_Lean_replaceRef(v_ref_1121_, v_ref_1130_);
lean_inc(v_currRecDepth_1129_);
lean_inc_ref(v_toCold_1128_);
v___x_1136_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1136_, 0, v_toCold_1128_);
lean_ctor_set(v___x_1136_, 1, v_currRecDepth_1129_);
lean_ctor_set(v___x_1136_, 2, v_ref_1135_);
lean_ctor_set_uint16(v___x_1136_, sizeof(void*)*3, v_optionFlags_1131_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3 + 2, v_suppressElabErrors_1132_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3 + 3, v_checkDeprecated_1133_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3 + 4, v_isRecordingDeps_1134_);
v___x_1137_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_1122_, v___y_1123_, v___y_1124_, v___x_1136_, v___y_1126_);
lean_dec_ref_known(v___x_1136_, 3);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg___boxed(lean_object* v_ref_1138_, lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(v_ref_1138_, v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1138_);
return v_res_1145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
lean_ctor_set(v___x_1151_, 2, v___x_1150_);
lean_ctor_set(v___x_1151_, 3, v___x_1150_);
lean_ctor_set(v___x_1151_, 4, v___x_1149_);
lean_ctor_set(v___x_1151_, 5, v___x_1149_);
lean_ctor_set(v___x_1151_, 6, v___x_1149_);
lean_ctor_set(v___x_1151_, 7, v___x_1149_);
lean_ctor_set(v___x_1151_, 8, v___x_1149_);
lean_ctor_set(v___x_1151_, 9, v___x_1149_);
lean_ctor_set(v___x_1151_, 10, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(32u);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1155_ = ((size_t)5ULL);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_unsigned_to_nat(32u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3);
v___x_1160_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
lean_ctor_set(v___x_1160_, 2, v___x_1156_);
lean_ctor_set(v___x_1160_, 3, v___x_1156_);
lean_ctor_set_usize(v___x_1160_, 4, v___x_1155_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1161_ = lean_box(1);
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4);
v___x_1163_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1);
v___x_1164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
lean_ctor_set(v___x_1164_, 2, v___x_1161_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__6));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__8));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__10));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__12));
v___x_1176_ = l_Lean_stringToMessageData(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__14));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__16));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__18));
v___x_1185_ = l_Lean_stringToMessageData(v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(lean_object* v_msg_1186_, lean_object* v_declHint_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_env_1192_; uint8_t v___x_1193_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_st_ref_get(v___y_1188_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = l_Lean_Name_isAnonymous(v_declHint_1187_);
if (v___x_1193_ == 0)
{
uint8_t v_isExporting_1194_; 
v_isExporting_1194_ = lean_ctor_get_uint8(v_env_1192_, sizeof(void*)*13);
if (v_isExporting_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v_env_1192_);
lean_dec(v_declHint_1187_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_msg_1186_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
lean_inc_ref(v_env_1192_);
v___x_1196_ = l_Lean_Environment_setExporting(v_env_1192_, v___x_1193_);
lean_inc(v_declHint_1187_);
lean_inc_ref(v___x_1196_);
v___x_1197_ = l_Lean_Environment_contains(v___x_1196_, v_declHint_1187_, v_isExporting_1194_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v___x_1196_);
lean_dec_ref(v_env_1192_);
lean_dec(v_declHint_1187_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_msg_1186_);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_c_1204_; lean_object* v___x_1205_; 
v___x_1199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2);
v___x_1200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5);
v___x_1201_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1196_);
v___x_1202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1196_);
lean_ctor_set(v___x_1202_, 1, v___x_1199_);
lean_ctor_set(v___x_1202_, 2, v___x_1200_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
lean_inc(v_declHint_1187_);
v___x_1203_ = l_Lean_MessageData_ofConstName(v_declHint_1187_, v___x_1193_);
v_c_1204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1204_, 0, v___x_1202_);
lean_ctor_set(v_c_1204_, 1, v___x_1203_);
v___x_1205_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1196_, v_declHint_1187_);
lean_dec_ref(v___x_1196_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_env_1192_);
lean_dec(v_declHint_1187_);
v___x_1206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v_c_1204_);
v___x_1208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_MessageData_note(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_msg_1186_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1247_; 
v_val_1213_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1215_ = v___x_1205_;
v_isShared_1216_ = v_isSharedCheck_1247_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_val_1213_);
lean_dec(v___x_1205_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1247_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v_moduleNames_1218_; lean_object* v_mod_1219_; uint8_t v___x_1220_; 
v___x_1217_ = l_Lean_Environment_header(v_env_1192_);
lean_dec_ref(v_env_1192_);
v_moduleNames_1218_ = lean_ctor_get(v___x_1217_, 4);
lean_inc_ref(v_moduleNames_1218_);
lean_dec_ref(v___x_1217_);
v_mod_1219_ = lean_array_get(v___x_1190_, v_moduleNames_1218_, v_val_1213_);
lean_dec(v_val_1213_);
lean_dec_ref(v_moduleNames_1218_);
v___x_1220_ = l_Lean_isPrivateName(v_declHint_1187_);
lean_dec(v_declHint_1187_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_c_1204_);
v___x_1223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_MessageData_ofName(v_mod_1219_);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_MessageData_note(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_msg_1186_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1230_);
v___x_1232_ = v___x_1215_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_c_1204_);
v___x_1236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_MessageData_ofName(v_mod_1219_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_MessageData_note(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_msg_1186_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1243_);
v___x_1245_ = v___x_1215_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1248_; 
lean_dec_ref(v_env_1192_);
lean_dec(v_declHint_1187_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_msg_1186_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___boxed(lean_object* v_msg_1249_, lean_object* v_declHint_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_1249_, v_declHint_1250_, v___y_1251_);
lean_dec(v___y_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(lean_object* v_msg_1254_, lean_object* v_declHint_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1271_; 
v___x_1261_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_1254_, v_declHint_1255_, v___y_1259_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1266_ = l_Lean_unknownIdentifierMessageTag;
v___x_1267_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_a_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17___boxed(lean_object* v_msg_1272_, lean_object* v_declHint_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(v_msg_1272_, v_declHint_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(lean_object* v_ref_1280_, lean_object* v_msg_1281_, lean_object* v_declHint_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v_a_1289_; lean_object* v___x_1290_; 
v___x_1288_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(v_msg_1281_, v_declHint_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(v_ref_1280_, v_a_1289_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg___boxed(lean_object* v_ref_1291_, lean_object* v_msg_1292_, lean_object* v_declHint_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(v_ref_1291_, v_msg_1292_, v_declHint_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v_ref_1291_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__0));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__2));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_1306_, lean_object* v_constName_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1313_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1);
v___x_1314_ = 0;
lean_inc(v_constName_1307_);
v___x_1315_ = l_Lean_MessageData_ofConstName(v_constName_1307_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1313_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(v_ref_1306_, v___x_1318_, v_constName_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_1320_, lean_object* v_constName_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_1320_, v_constName_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v_ref_1320_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(lean_object* v_constName_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_ref_1334_; lean_object* v___x_1335_; 
v_ref_1334_ = lean_ctor_get(v___y_1331_, 2);
v___x_1335_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_1334_, v_constName_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_constName_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(v_constName_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object* v_constName_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v_env_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = lean_st_ref_get(v___y_1347_);
v_env_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_ref(v_env_1350_);
lean_dec(v___x_1349_);
v___x_1351_ = 0;
lean_inc(v_constName_1343_);
v___x_1352_ = l_Lean_Environment_findConstVal_x3f(v_env_1350_, v_constName_1343_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(v_constName_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1353_;
}
else
{
lean_object* v_val_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_constName_1343_);
v_val_1354_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1352_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_val_1354_);
lean_dec(v___x_1352_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 0);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_val_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object* v_constName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_constName_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__1(lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
if (lean_obj_tag(v_a_1369_) == 0)
{
lean_object* v___x_1371_; 
v___x_1371_ = l_List_reverse___redArg(v_a_1370_);
return v___x_1371_;
}
else
{
lean_object* v_head_1372_; lean_object* v_tail_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1382_; 
v_head_1372_ = lean_ctor_get(v_a_1369_, 0);
v_tail_1373_ = lean_ctor_get(v_a_1369_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_a_1369_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1375_ = v_a_1369_;
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_tail_1373_);
lean_inc(v_head_1372_);
lean_dec(v_a_1369_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = l_Lean_mkLevelParam(v_head_1372_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v_a_1370_);
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_a_1370_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v_a_1369_ = v_tail_1373_;
v_a_1370_ = v___x_1379_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object* v_constName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
lean_inc(v_constName_1383_);
v___x_1389_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_constName_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1401_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1401_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1401_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_levelParams_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v_levelParams_1394_ = lean_ctor_get(v_a_1390_, 1);
lean_inc(v_levelParams_1394_);
lean_dec(v_a_1390_);
v___x_1395_ = lean_box(0);
v___x_1396_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__1(v_levelParams_1394_, v___x_1395_);
v___x_1397_ = l_Lean_mkConst(v_constName_1383_, v___x_1396_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1397_);
v___x_1399_ = v___x_1392_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_constName_1383_);
v_a_1402_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1389_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1389_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object* v_constName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_constName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(lean_object* v_as_1419_, size_t v_i_1420_, size_t v_stop_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_a_1429_; uint8_t v___x_1433_; 
v___x_1433_ = lean_usize_dec_eq(v_i_1420_, v_stop_1421_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_array_uget_borrowed(v_as_1419_, v_i_1420_);
lean_inc(v___x_1434_);
v___x_1435_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v___x_1434_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc_n(v_a_1436_, 2);
lean_dec_ref_known(v___x_1435_, 1);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
v___x_1437_ = lean_infer_type(v_a_1436_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = l_Lean_Meta_isClass_x3f(v_a_1438_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___closed__0));
v___x_1442_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_a_1440_, v___x_1441_);
lean_dec(v_a_1440_);
if (v___x_1442_ == 0)
{
lean_dec(v_a_1436_);
v_a_1429_ = v_b_1422_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1443_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3);
v___x_1444_ = l_Lean_MessageData_ofConst(v_a_1436_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___x_1443_);
v___x_1447_ = lean_array_push(v_b_1422_, v___x_1446_);
v_a_1429_ = v___x_1447_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_a_1436_);
lean_dec_ref(v_b_1422_);
v_a_1448_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1439_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1439_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1436_);
lean_dec_ref(v_b_1422_);
v_a_1456_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1437_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1437_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_b_1422_);
v_a_1464_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1435_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1435_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_b_1422_);
return v___x_1472_;
}
v___jp_1428_:
{
size_t v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1420_, v___x_1430_);
v_i_1420_ = v___x_1431_;
v_b_1422_ = v_a_1429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___boxed(lean_object* v_as_1473_, lean_object* v_i_1474_, lean_object* v_stop_1475_, lean_object* v_b_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
size_t v_i_boxed_1482_; size_t v_stop_boxed_1483_; lean_object* v_res_1484_; 
v_i_boxed_1482_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_stop_boxed_1483_ = lean_unbox_usize(v_stop_1475_);
lean_dec(v_stop_1475_);
v_res_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(v_as_1473_, v_i_boxed_1482_, v_stop_boxed_1483_, v_b_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec_ref(v_as_1473_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object* v_as_1487_, lean_object* v_start_1488_, lean_object* v_stop_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0));
v___x_1496_ = lean_nat_dec_lt(v_start_1488_, v_stop_1489_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = lean_array_get_size(v_as_1487_);
v___x_1499_ = lean_nat_dec_le(v_stop_1489_, v___x_1498_);
if (v___x_1499_ == 0)
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_nat_dec_lt(v_start_1488_, v___x_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1495_);
return v___x_1501_;
}
else
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_usize_of_nat(v_start_1488_);
v___x_1503_ = lean_usize_of_nat(v___x_1498_);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(v_as_1487_, v___x_1502_, v___x_1503_, v___x_1495_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1504_;
}
}
else
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_usize_of_nat(v_start_1488_);
v___x_1506_ = lean_usize_of_nat(v_stop_1489_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(v_as_1487_, v___x_1505_, v___x_1506_, v___x_1495_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object* v_as_1508_, lean_object* v_start_1509_, lean_object* v_stop_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v_as_1508_, v_start_1509_, v_stop_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_stop_1510_);
lean_dec(v_start_1509_);
lean_dec_ref(v_as_1508_);
return v_res_1516_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1);
v___x_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
lean_ctor_set(v___x_1522_, 3, v___x_1521_);
lean_ctor_set(v___x_1522_, 4, v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object* v___f_1527_, lean_object* v_s_1528_, uint8_t v___x_1529_, uint8_t v___x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint16_t v___y_1628_; lean_object* v___y_1629_; lean_object* v_fileName_1630_; lean_object* v_fileMap_1631_; lean_object* v_currNamespace_1632_; lean_object* v_openDecls_1633_; lean_object* v_initHeartbeats_1634_; lean_object* v_maxHeartbeats_1635_; lean_object* v_quotContext_1636_; lean_object* v_currMacroScope_1637_; lean_object* v_cancelTk_x3f_1638_; lean_object* v_inheritedTraceOptions_1639_; lean_object* v_currRecDepth_1640_; lean_object* v_ref_1641_; uint8_t v_suppressElabErrors_1642_; uint8_t v_checkDeprecated_1643_; uint8_t v_isRecordingDeps_1644_; lean_object* v___y_1645_; lean_object* v_toCold_1676_; lean_object* v_currRecDepth_1677_; lean_object* v_ref_1678_; uint8_t v_suppressElabErrors_1679_; uint8_t v_checkDeprecated_1680_; uint8_t v_isRecordingDeps_1681_; lean_object* v_fileName_1682_; lean_object* v_fileMap_1683_; lean_object* v_options_1684_; lean_object* v_currNamespace_1685_; lean_object* v_openDecls_1686_; lean_object* v_initHeartbeats_1687_; lean_object* v_maxHeartbeats_1688_; lean_object* v_quotContext_1689_; lean_object* v_currMacroScope_1690_; lean_object* v_cancelTk_x3f_1691_; lean_object* v_inheritedTraceOptions_1692_; uint8_t v___y_1694_; lean_object* v___y_1695_; uint16_t v___y_1696_; lean_object* v___y_1719_; 
v_toCold_1676_ = lean_ctor_get(v___y_1533_, 0);
v_currRecDepth_1677_ = lean_ctor_get(v___y_1533_, 1);
v_ref_1678_ = lean_ctor_get(v___y_1533_, 2);
v_suppressElabErrors_1679_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*3 + 2);
v_checkDeprecated_1680_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1681_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*3 + 4);
v_fileName_1682_ = lean_ctor_get(v_toCold_1676_, 0);
v_fileMap_1683_ = lean_ctor_get(v_toCold_1676_, 1);
v_options_1684_ = lean_ctor_get(v_toCold_1676_, 2);
v_currNamespace_1685_ = lean_ctor_get(v_toCold_1676_, 4);
v_openDecls_1686_ = lean_ctor_get(v_toCold_1676_, 5);
v_initHeartbeats_1687_ = lean_ctor_get(v_toCold_1676_, 6);
v_maxHeartbeats_1688_ = lean_ctor_get(v_toCold_1676_, 7);
v_quotContext_1689_ = lean_ctor_get(v_toCold_1676_, 8);
v_currMacroScope_1690_ = lean_ctor_get(v_toCold_1676_, 9);
v_cancelTk_x3f_1691_ = lean_ctor_get(v_toCold_1676_, 10);
v_inheritedTraceOptions_1692_ = lean_ctor_get(v_toCold_1676_, 11);
if (v_isRecordingDeps_1681_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1684_);
v___x_1729_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_options_1684_, v___x_1728_, v___x_1529_);
v___y_1719_ = v___x_1729_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1730_; 
lean_inc_ref(v_options_1684_);
v___x_1730_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1684_);
v___y_1719_ = v___x_1730_;
goto v___jp_1718_;
}
v___jp_1536_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_array_get_size(v___y_1541_);
v___x_1543_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v___y_1541_, v___y_1538_, v___x_1542_, v___y_1531_, v___y_1532_, v___y_1539_, v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___y_1537_);
lean_ctor_set(v___x_1548_, 1, v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v___y_1537_);
v_a_1553_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1543_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1543_);
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
v___jp_1561_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v___y_1562_, v___y_1568_, v___y_1566_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec(v___y_1562_);
v___y_1537_ = v___y_1563_;
v___y_1538_ = v___y_1564_;
v___y_1539_ = v___y_1565_;
v___y_1540_ = v___y_1567_;
v___y_1541_ = v___x_1570_;
goto v___jp_1536_;
}
v___jp_1571_:
{
uint8_t v___x_1580_; 
v___x_1580_ = lean_nat_dec_le(v___y_1579_, v___y_1578_);
if (v___x_1580_ == 0)
{
lean_dec(v___y_1578_);
lean_inc(v___y_1579_);
v___y_1562_ = v___y_1572_;
v___y_1563_ = v___y_1573_;
v___y_1564_ = v___y_1574_;
v___y_1565_ = v___y_1575_;
v___y_1566_ = v___y_1579_;
v___y_1567_ = v___y_1577_;
v___y_1568_ = v___y_1576_;
v___y_1569_ = v___y_1579_;
goto v___jp_1561_;
}
else
{
v___y_1562_ = v___y_1572_;
v___y_1563_ = v___y_1573_;
v___y_1564_ = v___y_1574_;
v___y_1565_ = v___y_1575_;
v___y_1566_ = v___y_1579_;
v___y_1567_ = v___y_1577_;
v___y_1568_ = v___y_1576_;
v___y_1569_ = v___y_1578_;
goto v___jp_1561_;
}
}
v___jp_1581_:
{
if (lean_obj_tag(v___y_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v_diag_1587_; lean_object* v_unfoldCounter_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_a_1585_ = lean_ctor_get(v___y_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___y_1584_, 1);
v___x_1586_ = lean_st_ref_get(v___y_1532_);
v_diag_1587_ = lean_ctor_get(v___x_1586_, 4);
lean_inc_ref(v_diag_1587_);
lean_dec(v___x_1586_);
v_unfoldCounter_1588_ = lean_ctor_get(v_diag_1587_, 0);
lean_inc_ref(v_unfoldCounter_1588_);
lean_dec_ref(v_diag_1587_);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_1591_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_unfoldCounter_1588_, v___f_1527_, v___x_1590_);
lean_dec_ref(v_unfoldCounter_1588_);
v___x_1592_ = lean_array_get_size(v___x_1591_);
v___x_1593_ = lean_nat_dec_eq(v___x_1592_, v___x_1589_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = lean_nat_sub(v___x_1592_, v___x_1594_);
v___x_1596_ = lean_nat_dec_le(v___x_1589_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_inc(v___x_1595_);
v___y_1572_ = v___x_1592_;
v___y_1573_ = v_a_1585_;
v___y_1574_ = v___x_1589_;
v___y_1575_ = v___y_1582_;
v___y_1576_ = v___x_1591_;
v___y_1577_ = v___y_1583_;
v___y_1578_ = v___x_1595_;
v___y_1579_ = v___x_1595_;
goto v___jp_1571_;
}
else
{
v___y_1572_ = v___x_1592_;
v___y_1573_ = v_a_1585_;
v___y_1574_ = v___x_1589_;
v___y_1575_ = v___y_1582_;
v___y_1576_ = v___x_1591_;
v___y_1577_ = v___y_1583_;
v___y_1578_ = v___x_1595_;
v___y_1579_ = v___x_1589_;
goto v___jp_1571_;
}
}
else
{
v___y_1537_ = v_a_1585_;
v___y_1538_ = v___x_1589_;
v___y_1539_ = v___y_1582_;
v___y_1540_ = v___y_1583_;
v___y_1541_ = v___x_1591_;
goto v___jp_1536_;
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___y_1582_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v___f_1527_);
v_a_1597_ = lean_ctor_get(v___y_1584_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___y_1584_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___y_1584_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___y_1584_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
v___jp_1605_:
{
lean_object* v___x_1608_; uint8_t v_transparency_1609_; uint8_t v___x_1610_; uint8_t v___x_1611_; 
v___x_1608_ = l_Lean_Meta_Context_config(v___y_1531_);
v_transparency_1609_ = lean_ctor_get_uint8(v___x_1608_, 9);
lean_dec_ref(v___x_1608_);
v___x_1610_ = 1;
v___x_1611_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_inc_ref(v___y_1606_);
v___x_1612_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1528_, v___y_1531_, v___y_1532_, v___y_1606_, v___y_1607_);
v___y_1582_ = v___y_1606_;
v___y_1583_ = v___y_1607_;
v___y_1584_ = v___x_1612_;
goto v___jp_1581_;
}
else
{
lean_object* v_keyedConfig_1613_; uint8_t v_trackZetaDelta_1614_; lean_object* v_zetaDeltaSet_1615_; lean_object* v_lctx_1616_; lean_object* v_localInstances_1617_; lean_object* v_defEqCtx_x3f_1618_; lean_object* v_synthPendingDepth_1619_; lean_object* v_customCanUnfoldPredicate_x3f_1620_; uint8_t v_univApprox_1621_; uint8_t v_inTypeClassResolution_1622_; uint8_t v_cacheInferType_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_keyedConfig_1613_ = lean_ctor_get(v___y_1531_, 0);
v_trackZetaDelta_1614_ = lean_ctor_get_uint8(v___y_1531_, sizeof(void*)*7);
v_zetaDeltaSet_1615_ = lean_ctor_get(v___y_1531_, 1);
v_lctx_1616_ = lean_ctor_get(v___y_1531_, 2);
v_localInstances_1617_ = lean_ctor_get(v___y_1531_, 3);
v_defEqCtx_x3f_1618_ = lean_ctor_get(v___y_1531_, 4);
v_synthPendingDepth_1619_ = lean_ctor_get(v___y_1531_, 5);
v_customCanUnfoldPredicate_x3f_1620_ = lean_ctor_get(v___y_1531_, 6);
v_univApprox_1621_ = lean_ctor_get_uint8(v___y_1531_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1622_ = lean_ctor_get_uint8(v___y_1531_, sizeof(void*)*7 + 2);
v_cacheInferType_1623_ = lean_ctor_get_uint8(v___y_1531_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1613_);
v___x_1624_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1610_, v_keyedConfig_1613_);
lean_inc(v_customCanUnfoldPredicate_x3f_1620_);
lean_inc(v_synthPendingDepth_1619_);
lean_inc(v_defEqCtx_x3f_1618_);
lean_inc_ref(v_localInstances_1617_);
lean_inc_ref(v_lctx_1616_);
lean_inc(v_zetaDeltaSet_1615_);
v___x_1625_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_zetaDeltaSet_1615_);
lean_ctor_set(v___x_1625_, 2, v_lctx_1616_);
lean_ctor_set(v___x_1625_, 3, v_localInstances_1617_);
lean_ctor_set(v___x_1625_, 4, v_defEqCtx_x3f_1618_);
lean_ctor_set(v___x_1625_, 5, v_synthPendingDepth_1619_);
lean_ctor_set(v___x_1625_, 6, v_customCanUnfoldPredicate_x3f_1620_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*7, v_trackZetaDelta_1614_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*7 + 1, v_univApprox_1621_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1622_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*7 + 3, v_cacheInferType_1623_);
lean_inc_ref(v___y_1606_);
v___x_1626_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1528_, v___x_1625_, v___y_1532_, v___y_1606_, v___y_1607_);
lean_dec_ref_known(v___x_1625_, 7);
v___y_1582_ = v___y_1606_;
v___y_1583_ = v___y_1607_;
v___y_1584_ = v___x_1626_;
goto v___jp_1581_;
}
}
v___jp_1627_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1646_ = l_Lean_maxRecDepth;
v___x_1647_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v___y_1629_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1648_, 0, v_fileName_1630_);
lean_ctor_set(v___x_1648_, 1, v_fileMap_1631_);
lean_ctor_set(v___x_1648_, 2, v___y_1629_);
lean_ctor_set(v___x_1648_, 3, v___x_1647_);
lean_ctor_set(v___x_1648_, 4, v_currNamespace_1632_);
lean_ctor_set(v___x_1648_, 5, v_openDecls_1633_);
lean_ctor_set(v___x_1648_, 6, v_initHeartbeats_1634_);
lean_ctor_set(v___x_1648_, 7, v_maxHeartbeats_1635_);
lean_ctor_set(v___x_1648_, 8, v_quotContext_1636_);
lean_ctor_set(v___x_1648_, 9, v_currMacroScope_1637_);
lean_ctor_set(v___x_1648_, 10, v_cancelTk_x3f_1638_);
lean_ctor_set(v___x_1648_, 11, v_inheritedTraceOptions_1639_);
lean_inc(v_ref_1641_);
lean_inc(v_currRecDepth_1640_);
v___x_1649_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_currRecDepth_1640_);
lean_ctor_set(v___x_1649_, 2, v_ref_1641_);
lean_ctor_set_uint16(v___x_1649_, sizeof(void*)*3, v___y_1628_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*3 + 2, v_suppressElabErrors_1642_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*3 + 3, v_checkDeprecated_1643_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*3 + 4, v_isRecordingDeps_1644_);
v___x_1650_ = l_Lean_isDiagnosticsEnabled___redArg(v___x_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; uint8_t v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
if (v___x_1652_ == 0)
{
v___y_1606_ = v___x_1649_;
v___y_1607_ = v___y_1645_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1653_; lean_object* v_mctx_1654_; lean_object* v_cache_1655_; lean_object* v_zetaDeltaFVarIds_1656_; lean_object* v_postponed_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1666_; 
v___x_1653_ = lean_st_ref_take(v___y_1532_);
v_mctx_1654_ = lean_ctor_get(v___x_1653_, 0);
v_cache_1655_ = lean_ctor_get(v___x_1653_, 1);
v_zetaDeltaFVarIds_1656_ = lean_ctor_get(v___x_1653_, 2);
v_postponed_1657_ = lean_ctor_get(v___x_1653_, 3);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v___x_1653_, 4);
lean_dec(v_unused_1667_);
v___x_1659_ = v___x_1653_;
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_postponed_1657_);
lean_inc(v_zetaDeltaFVarIds_1656_);
lean_inc(v_cache_1655_);
lean_inc(v_mctx_1654_);
lean_dec(v___x_1653_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_mctx_1654_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_cache_1655_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_zetaDeltaFVarIds_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_postponed_1657_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_st_ref_put(v___y_1532_, v___x_1663_);
v___y_1606_ = v___x_1649_;
v___y_1607_ = v___y_1645_;
goto v___jp_1605_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref_known(v___x_1649_, 3);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_s_1528_);
lean_dec_ref(v___f_1527_);
v_a_1668_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1650_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1650_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
v___jp_1693_:
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v_nextMacroScope_1699_; lean_object* v_ngen_1700_; lean_object* v_auxDeclNGen_1701_; lean_object* v_traceState_1702_; lean_object* v_recordedDeps_1703_; lean_object* v_messages_1704_; lean_object* v_infoState_1705_; lean_object* v_snapshotTasks_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1716_; 
v___x_1697_ = lean_st_ref_take(v___y_1534_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
v_nextMacroScope_1699_ = lean_ctor_get(v___x_1697_, 1);
v_ngen_1700_ = lean_ctor_get(v___x_1697_, 2);
v_auxDeclNGen_1701_ = lean_ctor_get(v___x_1697_, 3);
v_traceState_1702_ = lean_ctor_get(v___x_1697_, 4);
v_recordedDeps_1703_ = lean_ctor_get(v___x_1697_, 6);
v_messages_1704_ = lean_ctor_get(v___x_1697_, 7);
v_infoState_1705_ = lean_ctor_get(v___x_1697_, 8);
v_snapshotTasks_1706_ = lean_ctor_get(v___x_1697_, 9);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v___x_1697_, 5);
lean_dec(v_unused_1717_);
v___x_1708_ = v___x_1697_;
v_isShared_1709_ = v_isSharedCheck_1716_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snapshotTasks_1706_);
lean_inc(v_infoState_1705_);
lean_inc(v_messages_1704_);
lean_inc(v_recordedDeps_1703_);
lean_inc(v_traceState_1702_);
lean_inc(v_auxDeclNGen_1701_);
lean_inc(v_ngen_1700_);
lean_inc(v_nextMacroScope_1699_);
lean_inc(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1716_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1710_ = l_Lean_Kernel_enableDiag(v_env_1698_, v___y_1694_);
v___x_1711_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 5, v___x_1711_);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1713_ = v___x_1708_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_nextMacroScope_1699_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_ngen_1700_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_auxDeclNGen_1701_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v_traceState_1702_);
lean_ctor_set(v_reuseFailAlloc_1715_, 5, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1715_, 6, v_recordedDeps_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 7, v_messages_1704_);
lean_ctor_set(v_reuseFailAlloc_1715_, 8, v_infoState_1705_);
lean_ctor_set(v_reuseFailAlloc_1715_, 9, v_snapshotTasks_1706_);
v___x_1713_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_st_ref_put(v___y_1534_, v___x_1713_);
lean_inc_ref(v_inheritedTraceOptions_1692_);
lean_inc(v_cancelTk_x3f_1691_);
lean_inc(v_currMacroScope_1690_);
lean_inc(v_quotContext_1689_);
lean_inc(v_maxHeartbeats_1688_);
lean_inc(v_initHeartbeats_1687_);
lean_inc(v_openDecls_1686_);
lean_inc(v_currNamespace_1685_);
lean_inc_ref(v_fileMap_1683_);
lean_inc_ref(v_fileName_1682_);
v___y_1628_ = v___y_1696_;
v___y_1629_ = v___y_1695_;
v_fileName_1630_ = v_fileName_1682_;
v_fileMap_1631_ = v_fileMap_1683_;
v_currNamespace_1632_ = v_currNamespace_1685_;
v_openDecls_1633_ = v_openDecls_1686_;
v_initHeartbeats_1634_ = v_initHeartbeats_1687_;
v_maxHeartbeats_1635_ = v_maxHeartbeats_1688_;
v_quotContext_1636_ = v_quotContext_1689_;
v_currMacroScope_1637_ = v_currMacroScope_1690_;
v_cancelTk_x3f_1638_ = v_cancelTk_x3f_1691_;
v_inheritedTraceOptions_1639_ = v_inheritedTraceOptions_1692_;
v_currRecDepth_1640_ = v_currRecDepth_1677_;
v_ref_1641_ = v_ref_1678_;
v_suppressElabErrors_1642_ = v_suppressElabErrors_1679_;
v_checkDeprecated_1643_ = v_checkDeprecated_1680_;
v_isRecordingDeps_1644_ = v_isRecordingDeps_1681_;
v___y_1645_ = v___y_1534_;
goto v___jp_1627_;
}
}
}
v___jp_1718_:
{
uint16_t v___x_1720_; lean_object* v___x_1721_; lean_object* v_env_1722_; uint8_t v___x_1723_; uint16_t v___x_1724_; uint16_t v___x_1725_; uint16_t v___x_1726_; uint8_t v___x_1727_; 
v___x_1720_ = l_Lean_OptionFlags_ofOptions(v___y_1719_);
v___x_1721_ = lean_st_ref_get(v___y_1534_);
v_env_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc_ref(v_env_1722_);
lean_dec(v___x_1721_);
v___x_1723_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1722_);
lean_dec_ref(v_env_1722_);
v___x_1724_ = 512;
v___x_1725_ = lean_uint16_land(v___x_1720_, v___x_1724_);
v___x_1726_ = 0;
v___x_1727_ = lean_uint16_dec_eq(v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
if (v___x_1723_ == 0)
{
v___y_1694_ = v___x_1529_;
v___y_1695_ = v___y_1719_;
v___y_1696_ = v___x_1720_;
goto v___jp_1693_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1692_);
lean_inc(v_cancelTk_x3f_1691_);
lean_inc(v_currMacroScope_1690_);
lean_inc(v_quotContext_1689_);
lean_inc(v_maxHeartbeats_1688_);
lean_inc(v_initHeartbeats_1687_);
lean_inc(v_openDecls_1686_);
lean_inc(v_currNamespace_1685_);
lean_inc_ref(v_fileMap_1683_);
lean_inc_ref(v_fileName_1682_);
v___y_1628_ = v___x_1720_;
v___y_1629_ = v___y_1719_;
v_fileName_1630_ = v_fileName_1682_;
v_fileMap_1631_ = v_fileMap_1683_;
v_currNamespace_1632_ = v_currNamespace_1685_;
v_openDecls_1633_ = v_openDecls_1686_;
v_initHeartbeats_1634_ = v_initHeartbeats_1687_;
v_maxHeartbeats_1635_ = v_maxHeartbeats_1688_;
v_quotContext_1636_ = v_quotContext_1689_;
v_currMacroScope_1637_ = v_currMacroScope_1690_;
v_cancelTk_x3f_1638_ = v_cancelTk_x3f_1691_;
v_inheritedTraceOptions_1639_ = v_inheritedTraceOptions_1692_;
v_currRecDepth_1640_ = v_currRecDepth_1677_;
v_ref_1641_ = v_ref_1678_;
v_suppressElabErrors_1642_ = v_suppressElabErrors_1679_;
v_checkDeprecated_1643_ = v_checkDeprecated_1680_;
v_isRecordingDeps_1644_ = v_isRecordingDeps_1681_;
v___y_1645_ = v___y_1534_;
goto v___jp_1627_;
}
}
else
{
if (v___x_1723_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1692_);
lean_inc(v_cancelTk_x3f_1691_);
lean_inc(v_currMacroScope_1690_);
lean_inc(v_quotContext_1689_);
lean_inc(v_maxHeartbeats_1688_);
lean_inc(v_initHeartbeats_1687_);
lean_inc(v_openDecls_1686_);
lean_inc(v_currNamespace_1685_);
lean_inc_ref(v_fileMap_1683_);
lean_inc_ref(v_fileName_1682_);
v___y_1628_ = v___x_1720_;
v___y_1629_ = v___y_1719_;
v_fileName_1630_ = v_fileName_1682_;
v_fileMap_1631_ = v_fileMap_1683_;
v_currNamespace_1632_ = v_currNamespace_1685_;
v_openDecls_1633_ = v_openDecls_1686_;
v_initHeartbeats_1634_ = v_initHeartbeats_1687_;
v_maxHeartbeats_1635_ = v_maxHeartbeats_1688_;
v_quotContext_1636_ = v_quotContext_1689_;
v_currMacroScope_1637_ = v_currMacroScope_1690_;
v_cancelTk_x3f_1638_ = v_cancelTk_x3f_1691_;
v_inheritedTraceOptions_1639_ = v_inheritedTraceOptions_1692_;
v_currRecDepth_1640_ = v_currRecDepth_1677_;
v_ref_1641_ = v_ref_1678_;
v_suppressElabErrors_1642_ = v_suppressElabErrors_1679_;
v_checkDeprecated_1643_ = v_checkDeprecated_1680_;
v_isRecordingDeps_1644_ = v_isRecordingDeps_1681_;
v___y_1645_ = v___y_1534_;
goto v___jp_1627_;
}
else
{
v___y_1694_ = v___x_1530_;
v___y_1695_ = v___y_1719_;
v___y_1696_ = v___x_1720_;
goto v___jp_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object* v___f_1731_, lean_object* v_s_1732_, lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_11361__boxed_1740_; uint8_t v___x_11362__boxed_1741_; lean_object* v_res_1742_; 
v___x_11361__boxed_1740_ = lean_unbox(v___x_1733_);
v___x_11362__boxed_1741_ = lean_unbox(v___x_1734_);
v_res_1742_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(v___f_1731_, v_s_1732_, v___x_11361__boxed_1740_, v___x_11362__boxed_1741_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
return v_res_1742_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1));
v___x_1746_ = l_Lean_stringToMessageData(v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* v_tacticName_1816_, lean_object* v_expectedType_1817_, lean_object* v_s_1818_, lean_object* v_r_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_1826_ = l_Lean_Expr_isConstOf(v_r_1819_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___f_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___f_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_expectedType_1817_);
v___f_1827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0));
v___x_1828_ = 1;
v___x_1829_ = lean_box(v___x_1828_);
v___x_1830_ = lean_box(v___x_1826_);
lean_inc_ref(v_s_1818_);
v___f_1831_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1831_, 0, v___f_1827_);
lean_closure_set(v___f_1831_, 1, v_s_1818_);
lean_closure_set(v___f_1831_, 2, v___x_1829_);
lean_closure_set(v___f_1831_, 3, v___x_1830_);
v___x_1832_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v___f_1831_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1946_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1946_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1946_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1945_; 
v_fst_1864_ = lean_ctor_get(v_a_1833_, 0);
v_snd_1865_ = lean_ctor_get(v_a_1833_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1833_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1867_ = v_a_1833_;
v_isShared_1868_ = v_isSharedCheck_1945_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_inc(v_fst_1864_);
lean_dec(v_a_1833_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1945_;
goto v_resetjp_1866_;
}
v___jp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1840_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1841_ = l_Lean_MessageData_ofName(v_tacticName_1816_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_Expr_setPPExplicit(v_s_1818_, v___x_1828_);
v___x_1846_ = l_Lean_indentExpr(v___x_1845_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1844_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_1851_ = l_Lean_MessageData_ofConstName(v___x_1850_, v___x_1826_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1849_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_MessageData_ofConstName(v___x_1825_, v___x_1826_);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___y_1838_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___y_1839_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1860_);
v___x_1862_ = v___x_1835_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
v_resetjp_1866_:
{
lean_object* v___y_1870_; lean_object* v___y_1922_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_array_get_size(v_snd_1865_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_nat_dec_eq(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_unsigned_to_nat(1u);
v___x_1939_ = lean_nat_dec_eq(v___x_1935_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42));
v___y_1922_ = v___x_1940_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43));
v___y_1922_ = v___x_1941_;
goto v___jp_1921_;
}
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_snd_1865_);
v___x_1942_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45);
lean_inc(v_fst_1864_);
v___x_1943_ = l_Lean_indentExpr(v_fst_1864_);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___y_1870_ = v___x_1944_;
goto v___jp_1869_;
}
v___jp_1869_:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10));
v___x_1872_ = l_Lean_Expr_isAppOf(v_fst_1864_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13));
v___x_1874_ = l_Lean_Expr_isAppOf(v_fst_1864_, v___x_1873_);
lean_dec(v_fst_1864_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_del_object(v___x_1867_);
v___x_1875_ = l_Lean_MessageData_nil;
v___y_1838_ = v___y_1870_;
v___y_1839_ = v___x_1875_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1876_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15);
v___x_1877_ = l_Lean_MessageData_ofConstName(v___x_1873_, v___x_1872_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 7);
lean_ctor_set(v___x_1867_, 1, v___x_1877_);
lean_ctor_set(v___x_1867_, 0, v___x_1876_);
v___x_1879_ = v___x_1867_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1880_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4));
v___x_1883_ = l_Lean_MessageData_ofConstName(v___x_1882_, v___x_1872_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
lean_inc(v_tacticName_1816_);
v___x_1887_ = l_Lean_MessageData_ofName(v_tacticName_1816_);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23));
v___x_1892_ = l_Lean_MessageData_ofConstName(v___x_1891_, v___x_1872_);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1890_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_MessageData_hint_x27(v___x_1895_);
v___y_1838_ = v___y_1870_;
v___y_1839_ = v___x_1896_;
goto v___jp_1837_;
}
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v_fst_1864_);
v___x_1898_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25);
v___x_1899_ = l_Lean_MessageData_ofConstName(v___x_1871_, v___x_1826_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 7);
lean_ctor_set(v___x_1867_, 1, v___x_1899_);
lean_ctor_set(v___x_1867_, 0, v___x_1898_);
v___x_1901_ = v___x_1867_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4));
v___x_1905_ = l_Lean_MessageData_ofConstName(v___x_1904_, v___x_1826_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1903_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31));
v___x_1910_ = l_Lean_MessageData_ofConstName(v___x_1909_, v___x_1826_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1908_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33));
v___x_1915_ = l_Lean_MessageData_ofConstName(v___x_1914_, v___x_1826_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_MessageData_hint_x27(v___x_1918_);
v___y_1838_ = v___y_1870_;
v___y_1839_ = v___x_1919_;
goto v___jp_1837_;
}
}
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37);
lean_inc_ref(v___y_1922_);
v___x_1924_ = l_Lean_stringToMessageData(v___y_1922_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_array_to_list(v_snd_1865_);
v___x_1929_ = l_Lean_MessageData_andList(v___x_1928_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1927_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
lean_inc(v_fst_1864_);
v___x_1933_ = l_Lean_indentExpr(v_fst_1864_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___y_1870_ = v___x_1934_;
goto v___jp_1869_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_s_1818_);
lean_dec(v_tacticName_1816_);
v_a_1947_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1832_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1832_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v_s_1818_);
v___x_1955_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1956_ = l_Lean_MessageData_ofName(v_tacticName_1816_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = l_Lean_indentExpr(v_expectedType_1817_);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object* v_tacticName_1965_, lean_object* v_expectedType_1966_, lean_object* v_s_1967_, lean_object* v_r_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_1965_, v_expectedType_1966_, v_s_1967_, v_r_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec_ref(v_r_1968_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object* v_00_u03c3_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_map_1977_, lean_object* v_f_1978_, lean_object* v_init_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_1977_, v_f_1978_, v_init_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object* v_00_u03c3_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_map_1983_, lean_object* v_f_1984_, lean_object* v_init_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_00_u03c3_1981_, v_00_u03b2_1982_, v_map_1983_, v_f_1984_, v_init_1985_);
lean_dec_ref(v_map_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object* v_n_1987_, lean_object* v_as_1988_, lean_object* v_lo_1989_, lean_object* v_hi_1990_, lean_object* v_w_1991_, lean_object* v_hlo_1992_, lean_object* v_hhi_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_1987_, v_as_1988_, v_lo_1989_, v_hi_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object* v_n_1995_, lean_object* v_as_1996_, lean_object* v_lo_1997_, lean_object* v_hi_1998_, lean_object* v_w_1999_, lean_object* v_hlo_2000_, lean_object* v_hhi_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v_n_1995_, v_as_1996_, v_lo_1997_, v_hi_1998_, v_w_1999_, v_hlo_2000_, v_hhi_2001_);
lean_dec(v_hi_1998_);
lean_dec(v_n_1995_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___redArg(lean_object* v_map_2003_, lean_object* v_f_2004_, lean_object* v_init_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(v_f_2004_, v_map_2003_, v_init_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___redArg___boxed(lean_object* v_map_2007_, lean_object* v_f_2008_, lean_object* v_init_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___redArg(v_map_2007_, v_f_2008_, v_init_2009_);
lean_dec_ref(v_map_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5(lean_object* v_00_u03c3_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_map_2013_, lean_object* v_f_2014_, lean_object* v_init_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(v_f_2014_, v_map_2013_, v_init_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5___boxed(lean_object* v_00_u03c3_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_map_2019_, lean_object* v_f_2020_, lean_object* v_init_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5(v_00_u03c3_2017_, v_00_u03b2_2018_, v_map_2019_, v_f_2020_, v_init_2021_);
lean_dec_ref(v_map_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(lean_object* v_n_2023_, lean_object* v_lo_2024_, lean_object* v_hi_2025_, lean_object* v_hhi_2026_, lean_object* v_pivot_2027_, lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_k_2030_, lean_object* v_ilo_2031_, lean_object* v_ik_2032_, lean_object* v_w_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___redArg(v_hi_2025_, v_pivot_2027_, v_as_2028_, v_i_2029_, v_k_2030_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___boxed(lean_object* v_n_2035_, lean_object* v_lo_2036_, lean_object* v_hi_2037_, lean_object* v_hhi_2038_, lean_object* v_pivot_2039_, lean_object* v_as_2040_, lean_object* v_i_2041_, lean_object* v_k_2042_, lean_object* v_ilo_2043_, lean_object* v_ik_2044_, lean_object* v_w_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_n_2035_, v_lo_2036_, v_hi_2037_, v_hhi_2038_, v_pivot_2039_, v_as_2040_, v_i_2041_, v_k_2042_, v_ilo_2043_, v_ik_2044_, v_w_2045_);
lean_dec(v_pivot_2039_);
lean_dec(v_hi_2037_);
lean_dec(v_lo_2036_);
lean_dec(v_n_2035_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2047_, lean_object* v_constName_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(v_constName_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_constName_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4(v_00_u03b1_2055_, v_constName_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8(lean_object* v_00_u03c3_2063_, lean_object* v_00_u03b1_2064_, lean_object* v_00_u03b2_2065_, lean_object* v_f_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___redArg(v_f_2066_, v_x_2067_, v_x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03c3_2070_, lean_object* v_00_u03b1_2071_, lean_object* v_00_u03b2_2072_, lean_object* v_f_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8(v_00_u03c3_2070_, v_00_u03b1_2071_, v_00_u03b2_2072_, v_f_2073_, v_x_2074_, v_x_2075_);
lean_dec_ref(v_x_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2077_, lean_object* v_ref_2078_, lean_object* v_constName_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2078_, v_constName_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_ref_2087_, lean_object* v_constName_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2086_, v_ref_2087_, v_constName_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v_ref_2087_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_00_u03c3_2097_, lean_object* v_f_2098_, lean_object* v_as_2099_, size_t v_i_2100_, size_t v_stop_2101_, lean_object* v_b_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___redArg(v_f_2098_, v_as_2099_, v_i_2100_, v_stop_2101_, v_b_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_00_u03c3_2106_, lean_object* v_f_2107_, lean_object* v_as_2108_, lean_object* v_i_2109_, lean_object* v_stop_2110_, lean_object* v_b_2111_){
_start:
{
size_t v_i_boxed_2112_; size_t v_stop_boxed_2113_; lean_object* v_res_2114_; 
v_i_boxed_2112_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_stop_boxed_2113_ = lean_unbox_usize(v_stop_2110_);
lean_dec(v_stop_2110_);
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__14(v_00_u03b1_2104_, v_00_u03b2_2105_, v_00_u03c3_2106_, v_f_2107_, v_as_2108_, v_i_boxed_2112_, v_stop_boxed_2113_, v_b_2111_);
lean_dec_ref(v_as_2108_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15(lean_object* v_00_u03c3_2115_, lean_object* v_00_u03b1_2116_, lean_object* v_00_u03b2_2117_, lean_object* v_f_2118_, lean_object* v_keys_2119_, lean_object* v_vals_2120_, lean_object* v_heq_2121_, lean_object* v_i_2122_, lean_object* v_acc_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___redArg(v_f_2118_, v_keys_2119_, v_vals_2120_, v_i_2122_, v_acc_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15___boxed(lean_object* v_00_u03c3_2125_, lean_object* v_00_u03b1_2126_, lean_object* v_00_u03b2_2127_, lean_object* v_f_2128_, lean_object* v_keys_2129_, lean_object* v_vals_2130_, lean_object* v_heq_2131_, lean_object* v_i_2132_, lean_object* v_acc_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__5_spec__8_spec__15(v_00_u03c3_2125_, v_00_u03b1_2126_, v_00_u03b2_2127_, v_f_2128_, v_keys_2129_, v_vals_2130_, v_heq_2131_, v_i_2132_, v_acc_2133_);
lean_dec_ref(v_vals_2130_);
lean_dec_ref(v_keys_2129_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15(lean_object* v_00_u03b1_2135_, lean_object* v_ref_2136_, lean_object* v_msg_2137_, lean_object* v_declHint_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(v_ref_2136_, v_msg_2137_, v_declHint_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_ref_2146_, lean_object* v_msg_2147_, lean_object* v_declHint_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15(v_00_u03b1_2145_, v_ref_2146_, v_msg_2147_, v_declHint_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v_ref_2146_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20(lean_object* v_msg_2155_, lean_object* v_declHint_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_2155_, v_declHint_2156_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___boxed(lean_object* v_msg_2163_, lean_object* v_declHint_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20(v_msg_2163_, v_declHint_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18(lean_object* v_00_u03b1_2171_, lean_object* v_ref_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(v_ref_2172_, v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_ref_2181_, lean_object* v_msg_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18(v_00_u03b1_2180_, v_ref_2181_, v_msg_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v_ref_2181_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22(lean_object* v_00_u03b1_2189_, lean_object* v_msg_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_msg_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22(v_00_u03b1_2197_, v_msg_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = l_Lean_Level_ofNat(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1);
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2);
v___x_2213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__0));
v___x_2214_ = l_Lean_mkConst(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_box(0);
v___x_2216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3));
v___x_2217_ = l_Lean_mkConst(v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_2220_ = l_Lean_mkConst(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object* v_tacticName_2221_, lean_object* v_expectedType_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; 
lean_inc_ref(v_expectedType_2222_);
v___x_2228_ = l_Lean_Meta_mkDecide(v_expectedType_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; uint8_t v_transparency_2231_; lean_object* v___x_2232_; lean_object* v___y_2234_; uint8_t v___x_2267_; uint8_t v___x_2268_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = l_Lean_Meta_Context_config(v_a_2223_);
v_transparency_2231_ = lean_ctor_get_uint8(v___x_2230_, 9);
lean_dec_ref(v___x_2230_);
v___x_2232_ = l_Lean_Expr_appArg_x21(v_a_2229_);
v___x_2267_ = 1;
v___x_2268_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2231_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc_ref(v_a_2223_);
lean_inc(v_a_2229_);
v___x_2269_ = lean_whnf(v_a_2229_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
v___y_2234_ = v___x_2269_;
goto v___jp_2233_;
}
else
{
lean_object* v_keyedConfig_2270_; uint8_t v_trackZetaDelta_2271_; lean_object* v_zetaDeltaSet_2272_; lean_object* v_lctx_2273_; lean_object* v_localInstances_2274_; lean_object* v_defEqCtx_x3f_2275_; lean_object* v_synthPendingDepth_2276_; lean_object* v_customCanUnfoldPredicate_x3f_2277_; uint8_t v_univApprox_2278_; uint8_t v_inTypeClassResolution_2279_; uint8_t v_cacheInferType_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_keyedConfig_2270_ = lean_ctor_get(v_a_2223_, 0);
v_trackZetaDelta_2271_ = lean_ctor_get_uint8(v_a_2223_, sizeof(void*)*7);
v_zetaDeltaSet_2272_ = lean_ctor_get(v_a_2223_, 1);
v_lctx_2273_ = lean_ctor_get(v_a_2223_, 2);
v_localInstances_2274_ = lean_ctor_get(v_a_2223_, 3);
v_defEqCtx_x3f_2275_ = lean_ctor_get(v_a_2223_, 4);
v_synthPendingDepth_2276_ = lean_ctor_get(v_a_2223_, 5);
v_customCanUnfoldPredicate_x3f_2277_ = lean_ctor_get(v_a_2223_, 6);
v_univApprox_2278_ = lean_ctor_get_uint8(v_a_2223_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2279_ = lean_ctor_get_uint8(v_a_2223_, sizeof(void*)*7 + 2);
v_cacheInferType_2280_ = lean_ctor_get_uint8(v_a_2223_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2270_);
v___x_2281_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2267_, v_keyedConfig_2270_);
lean_inc(v_customCanUnfoldPredicate_x3f_2277_);
lean_inc(v_synthPendingDepth_2276_);
lean_inc(v_defEqCtx_x3f_2275_);
lean_inc_ref(v_localInstances_2274_);
lean_inc_ref(v_lctx_2273_);
lean_inc(v_zetaDeltaSet_2272_);
v___x_2282_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_zetaDeltaSet_2272_);
lean_ctor_set(v___x_2282_, 2, v_lctx_2273_);
lean_ctor_set(v___x_2282_, 3, v_localInstances_2274_);
lean_ctor_set(v___x_2282_, 4, v_defEqCtx_x3f_2275_);
lean_ctor_set(v___x_2282_, 5, v_synthPendingDepth_2276_);
lean_ctor_set(v___x_2282_, 6, v_customCanUnfoldPredicate_x3f_2277_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*7, v_trackZetaDelta_2271_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*7 + 1, v_univApprox_2278_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2279_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*7 + 3, v_cacheInferType_2280_);
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc(v_a_2229_);
v___x_2283_ = lean_whnf(v_a_2229_, v___x_2282_, v_a_2224_, v_a_2225_, v_a_2226_);
v___y_2234_ = v___x_2283_;
goto v___jp_2233_;
}
v___jp_2233_:
{
if (lean_obj_tag(v___y_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2258_; 
v_a_2235_ = lean_ctor_get(v___y_2234_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___y_2234_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2237_ = v___y_2234_;
v_isShared_2238_ = v_isSharedCheck_2258_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___y_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2258_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_2240_ = l_Lean_Expr_isConstOf(v_a_2235_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_del_object(v___x_2237_);
lean_dec_ref(v___x_2232_);
lean_inc_ref(v_expectedType_2222_);
v___x_2241_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed), 9, 4);
lean_closure_set(v___x_2241_, 0, v_tacticName_2221_);
lean_closure_set(v___x_2241_, 1, v_expectedType_2222_);
lean_closure_set(v___x_2241_, 2, v_a_2229_);
lean_closure_set(v___x_2241_, 3, v_a_2235_);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_mk_empty_array_with_capacity(v___x_2242_);
v___x_2244_ = lean_array_push(v___x_2243_, v_expectedType_2222_);
v___x_2245_ = l_Lean_MessageData_ofLazyM(v___x_2241_, v___x_2244_);
v___x_2246_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2245_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
lean_dec(v_a_2235_);
lean_dec(v_tacticName_2221_);
v___x_2247_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3);
v___x_2248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4);
v___x_2249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5);
v___x_2250_ = l_Lean_mkApp3(v___x_2247_, v___x_2248_, v_a_2229_, v___x_2249_);
v___x_2251_ = l_Lean_reflBoolTrue;
v___x_2252_ = l_Lean_Meta_mkExpectedPropHint(v___x_2251_, v___x_2250_);
v___x_2253_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_2254_ = l_Lean_mkApp3(v___x_2253_, v_expectedType_2222_, v___x_2232_, v___x_2252_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2254_);
v___x_2256_ = v___x_2237_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
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
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec_ref(v___x_2232_);
lean_dec(v_a_2229_);
lean_dec_ref(v_expectedType_2222_);
lean_dec(v_tacticName_2221_);
v_a_2259_ = lean_ctor_get(v___y_2234_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___y_2234_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___y_2234_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___y_2234_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2222_);
lean_dec(v_tacticName_2221_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(lean_object* v_tacticName_2284_, lean_object* v_expectedType_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2284_, v_expectedType_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* v_tacticName_2292_, lean_object* v_expectedType_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2292_, v_expectedType_2293_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* v_tacticName_2304_, lean_object* v_expectedType_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(v_tacticName_2304_, v_expectedType_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0));
v___x_2318_ = l_Lean_stringToMessageData(v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2));
v___x_2321_ = l_Lean_stringToMessageData(v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object* v_a_2322_, lean_object* v_tacticName_2323_, lean_object* v_expectedType_2324_, lean_object* v___x_2325_, lean_object* v___x_2326_, uint8_t v___x_2327_, uint8_t v___x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___y_2335_; lean_object* v_a_2336_; lean_object* v___y_2341_; lean_object* v___x_2375_; uint8_t v_transparency_2376_; uint8_t v___x_2377_; 
v___x_2375_ = l_Lean_Meta_Context_config(v___y_2329_);
v_transparency_2376_ = lean_ctor_get_uint8(v___x_2375_, 9);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2376_, v___x_2328_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; 
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc_ref(v___x_2325_);
v___x_2378_ = lean_whnf(v___x_2325_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
v___y_2341_ = v___x_2378_;
goto v___jp_2340_;
}
else
{
lean_object* v_keyedConfig_2379_; uint8_t v_trackZetaDelta_2380_; lean_object* v_zetaDeltaSet_2381_; lean_object* v_lctx_2382_; lean_object* v_localInstances_2383_; lean_object* v_defEqCtx_x3f_2384_; lean_object* v_synthPendingDepth_2385_; lean_object* v_customCanUnfoldPredicate_x3f_2386_; uint8_t v_univApprox_2387_; uint8_t v_inTypeClassResolution_2388_; uint8_t v_cacheInferType_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_keyedConfig_2379_ = lean_ctor_get(v___y_2329_, 0);
v_trackZetaDelta_2380_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*7);
v_zetaDeltaSet_2381_ = lean_ctor_get(v___y_2329_, 1);
v_lctx_2382_ = lean_ctor_get(v___y_2329_, 2);
v_localInstances_2383_ = lean_ctor_get(v___y_2329_, 3);
v_defEqCtx_x3f_2384_ = lean_ctor_get(v___y_2329_, 4);
v_synthPendingDepth_2385_ = lean_ctor_get(v___y_2329_, 5);
v_customCanUnfoldPredicate_x3f_2386_ = lean_ctor_get(v___y_2329_, 6);
v_univApprox_2387_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2388_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*7 + 2);
v_cacheInferType_2389_ = lean_ctor_get_uint8(v___y_2329_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2379_);
v___x_2390_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2328_, v_keyedConfig_2379_);
lean_inc(v_customCanUnfoldPredicate_x3f_2386_);
lean_inc(v_synthPendingDepth_2385_);
lean_inc(v_defEqCtx_x3f_2384_);
lean_inc_ref(v_localInstances_2383_);
lean_inc_ref(v_lctx_2382_);
lean_inc(v_zetaDeltaSet_2381_);
v___x_2391_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v_zetaDeltaSet_2381_);
lean_ctor_set(v___x_2391_, 2, v_lctx_2382_);
lean_ctor_set(v___x_2391_, 3, v_localInstances_2383_);
lean_ctor_set(v___x_2391_, 4, v_defEqCtx_x3f_2384_);
lean_ctor_set(v___x_2391_, 5, v_synthPendingDepth_2385_);
lean_ctor_set(v___x_2391_, 6, v_customCanUnfoldPredicate_x3f_2386_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7, v_trackZetaDelta_2380_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7 + 1, v_univApprox_2387_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2388_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7 + 3, v_cacheInferType_2389_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___x_2325_);
v___x_2392_ = lean_whnf(v___x_2325_, v___x_2391_, v___y_2330_, v___y_2331_, v___y_2332_);
v___y_2341_ = v___x_2392_;
goto v___jp_2340_;
}
v___jp_2334_:
{
uint8_t v___x_2337_; 
v___x_2337_ = l_Lean_Exception_isInterrupt(v_a_2336_);
lean_dec_ref(v_a_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v___y_2335_);
v___x_2338_ = l_Lean_Exception_toMessageData(v_a_2322_);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
else
{
lean_dec_ref(v_a_2322_);
return v___y_2335_;
}
}
v___jp_2340_:
{
if (lean_obj_tag(v___y_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2366_; 
v_a_2342_ = lean_ctor_get(v___y_2341_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2344_ = v___y_2341_;
v_isShared_2345_ = v_isSharedCheck_2366_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___y_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2366_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_2347_ = l_Lean_Expr_isConstOf(v_a_2342_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_del_object(v___x_2344_);
lean_dec_ref(v___x_2326_);
v___x_2348_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_2323_, v_expectedType_2324_, v___x_2325_, v_a_2342_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec_ref(v___y_2329_);
lean_dec(v_a_2342_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec_ref(v_a_2322_);
return v___x_2348_;
}
else
{
lean_object* v_a_2349_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
v___y_2335_ = v___x_2348_;
v_a_2336_ = v_a_2349_;
goto v___jp_2334_;
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec(v_a_2342_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_expectedType_2324_);
v___x_2350_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2351_ = l_Lean_MessageData_ofName(v_tacticName_2323_);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = l_Lean_Name_mkStr1(v___x_2326_);
v___x_2356_ = l_Lean_MessageData_ofConstName(v___x_2355_, v___x_2327_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_Exception_toMessageData(v_a_2322_);
v___x_2361_ = l_Lean_indentD(v___x_2360_);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2359_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2362_);
v___x_2364_ = v___x_2344_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v___y_2329_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_expectedType_2324_);
lean_dec(v_tacticName_2323_);
v_a_2367_ = lean_ctor_get(v___y_2341_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___y_2341_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___y_2341_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
lean_inc(v_a_2367_);
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
v___y_2335_ = v___x_2372_;
v_a_2336_ = v_a_2367_;
goto v___jp_2334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object* v_a_2393_, lean_object* v_tacticName_2394_, lean_object* v_expectedType_2395_, lean_object* v___x_2396_, lean_object* v___x_2397_, lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v___x_6951__boxed_2405_; uint8_t v___x_6952__boxed_2406_; lean_object* v_res_2407_; 
v___x_6951__boxed_2405_ = lean_unbox(v___x_2398_);
v___x_6952__boxed_2406_ = lean_unbox(v___x_2399_);
v_res_2407_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(v_a_2393_, v_tacticName_2394_, v_expectedType_2395_, v___x_2396_, v___x_2397_, v___x_6951__boxed_2405_, v___x_6952__boxed_2406_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
return v_res_2407_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(lean_object* v_a_2408_, lean_object* v_as_2409_, size_t v_i_2410_, size_t v_stop_2411_){
_start:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_usize_dec_eq(v_i_2410_, v_stop_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = lean_array_uget_borrowed(v_as_2409_, v_i_2410_);
v___x_2414_ = lean_name_eq(v_a_2408_, v___x_2413_);
if (v___x_2414_ == 0)
{
size_t v___x_2415_; size_t v___x_2416_; 
v___x_2415_ = ((size_t)1ULL);
v___x_2416_ = lean_usize_add(v_i_2410_, v___x_2415_);
v_i_2410_ = v___x_2416_;
goto _start;
}
else
{
return v___x_2414_;
}
}
else
{
uint8_t v___x_2418_; 
v___x_2418_ = 0;
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(lean_object* v_a_2419_, lean_object* v_as_2420_, lean_object* v_i_2421_, lean_object* v_stop_2422_){
_start:
{
size_t v_i_boxed_2423_; size_t v_stop_boxed_2424_; uint8_t v_res_2425_; lean_object* v_r_2426_; 
v_i_boxed_2423_ = lean_unbox_usize(v_i_2421_);
lean_dec(v_i_2421_);
v_stop_boxed_2424_ = lean_unbox_usize(v_stop_2422_);
lean_dec(v_stop_2422_);
v_res_2425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2419_, v_as_2420_, v_i_boxed_2423_, v_stop_boxed_2424_);
lean_dec_ref(v_as_2420_);
lean_dec(v_a_2419_);
v_r_2426_ = lean_box(v_res_2425_);
return v_r_2426_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object* v_as_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = lean_array_get_size(v_as_2427_);
v___x_2431_ = lean_nat_dec_lt(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
return v___x_2431_;
}
else
{
size_t v___x_2432_; size_t v___x_2433_; uint8_t v___x_2434_; 
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = lean_usize_of_nat(v___x_2430_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2428_, v_as_2427_, v___x_2432_, v___x_2433_);
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object* v_as_2435_, lean_object* v_a_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v_as_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_as_2435_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(lean_object* v___x_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
if (lean_obj_tag(v_a_2440_) == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = l_List_reverse___redArg(v_a_2441_);
return v___x_2442_;
}
else
{
lean_object* v_head_2443_; lean_object* v_tail_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2454_; 
v_head_2443_ = lean_ctor_get(v_a_2440_, 0);
v_tail_2444_ = lean_ctor_get(v_a_2440_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_a_2440_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2446_ = v_a_2440_;
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_tail_2444_);
lean_inc(v_head_2443_);
lean_dec(v_a_2440_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v___x_2439_, v_head_2443_);
if (v___x_2448_ == 0)
{
lean_del_object(v___x_2446_);
lean_dec(v_head_2443_);
v_a_2440_ = v_tail_2444_;
goto _start;
}
else
{
lean_object* v___x_2451_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v_a_2441_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_head_2443_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_a_2441_);
v___x_2451_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
v_a_2440_ = v_tail_2444_;
v_a_2441_ = v___x_2451_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(lean_object* v___x_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v___x_2455_, v_a_2456_, v_a_2457_);
lean_dec_ref(v___x_2455_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
if (lean_obj_tag(v_a_2459_) == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = l_List_reverse___redArg(v_a_2460_);
return v___x_2461_;
}
else
{
lean_object* v_head_2462_; lean_object* v_tail_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2472_; 
v_head_2462_ = lean_ctor_get(v_a_2459_, 0);
v_tail_2463_ = lean_ctor_get(v_a_2459_, 1);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_a_2459_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2465_ = v_a_2459_;
v_isShared_2466_ = v_isSharedCheck_2472_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_tail_2463_);
lean_inc(v_head_2462_);
lean_dec(v_a_2459_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2472_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = l_Lean_Level_param___override(v_head_2462_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v_a_2460_);
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_a_2460_);
v___x_2469_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
v_a_2459_ = v_tail_2463_;
v_a_2460_ = v___x_2469_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_box(0);
v___x_2474_ = lean_unsigned_to_nat(16u);
v___x_2475_ = lean_mk_array(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0);
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1);
v___x_2481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
lean_ctor_set(v___x_2481_, 2, v___x_2479_);
return v___x_2481_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_box(0);
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4));
v___x_2488_ = l_Lean_mkConst(v___x_2487_, v___x_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object* v_tacticName_2489_, lean_object* v_expectedType_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
lean_inc_ref(v_expectedType_2490_);
v___x_2499_ = l_Lean_Meta_mkDecideProof(v_expectedType_2490_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_params_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2);
lean_inc_ref(v_expectedType_2490_);
v___x_2502_ = l_Lean_collectLevelParams(v___x_2501_, v_expectedType_2490_);
v_params_2503_ = lean_ctor_get(v___x_2502_, 2);
lean_inc_ref(v_params_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = l_Lean_Expr_appFn_x21(v_a_2500_);
v___x_2505_ = l_Lean_Expr_appArg_x21(v___x_2504_);
lean_dec_ref(v___x_2504_);
v___x_2506_ = l_Lean_Elab_Term_getLevelNames___redArg(v_a_2493_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = l_List_reverse___redArg(v_a_2507_);
v___x_2509_ = lean_box(0);
v___x_2510_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v_params_2503_, v___x_2508_, v___x_2509_);
lean_dec_ref(v_params_2503_);
v___x_2511_ = lean_box(0);
v___x_2512_ = 1;
v___x_2513_ = 0;
v___x_2514_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_2491_, v_a_2493_, v_a_2495_, v_a_2497_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; uint16_t v___y_2517_; lean_object* v___y_2518_; lean_object* v_fileName_2519_; lean_object* v_fileMap_2520_; lean_object* v_currNamespace_2521_; lean_object* v_openDecls_2522_; lean_object* v_initHeartbeats_2523_; lean_object* v_maxHeartbeats_2524_; lean_object* v_quotContext_2525_; lean_object* v_currMacroScope_2526_; lean_object* v_cancelTk_x3f_2527_; lean_object* v_inheritedTraceOptions_2528_; lean_object* v_currRecDepth_2529_; lean_object* v_ref_2530_; uint8_t v_suppressElabErrors_2531_; uint8_t v_checkDeprecated_2532_; uint8_t v_isRecordingDeps_2533_; lean_object* v___y_2534_; lean_object* v_toCold_2584_; lean_object* v_currRecDepth_2585_; lean_object* v_ref_2586_; uint8_t v_suppressElabErrors_2587_; uint8_t v_checkDeprecated_2588_; uint8_t v_isRecordingDeps_2589_; lean_object* v_fileName_2590_; lean_object* v_fileMap_2591_; lean_object* v_options_2592_; lean_object* v_currNamespace_2593_; lean_object* v_openDecls_2594_; lean_object* v_initHeartbeats_2595_; lean_object* v_maxHeartbeats_2596_; lean_object* v_quotContext_2597_; lean_object* v_currMacroScope_2598_; lean_object* v_cancelTk_x3f_2599_; lean_object* v_inheritedTraceOptions_2600_; uint16_t v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2627_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v_toCold_2584_ = lean_ctor_get(v_a_2496_, 0);
v_currRecDepth_2585_ = lean_ctor_get(v_a_2496_, 1);
v_ref_2586_ = lean_ctor_get(v_a_2496_, 2);
v_suppressElabErrors_2587_ = lean_ctor_get_uint8(v_a_2496_, sizeof(void*)*3 + 2);
v_checkDeprecated_2588_ = lean_ctor_get_uint8(v_a_2496_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2589_ = lean_ctor_get_uint8(v_a_2496_, sizeof(void*)*3 + 4);
v_fileName_2590_ = lean_ctor_get(v_toCold_2584_, 0);
v_fileMap_2591_ = lean_ctor_get(v_toCold_2584_, 1);
v_options_2592_ = lean_ctor_get(v_toCold_2584_, 2);
v_currNamespace_2593_ = lean_ctor_get(v_toCold_2584_, 4);
v_openDecls_2594_ = lean_ctor_get(v_toCold_2584_, 5);
v_initHeartbeats_2595_ = lean_ctor_get(v_toCold_2584_, 6);
v_maxHeartbeats_2596_ = lean_ctor_get(v_toCold_2584_, 7);
v_quotContext_2597_ = lean_ctor_get(v_toCold_2584_, 8);
v_currMacroScope_2598_ = lean_ctor_get(v_toCold_2584_, 9);
v_cancelTk_x3f_2599_ = lean_ctor_get(v_toCold_2584_, 10);
v_inheritedTraceOptions_2600_ = lean_ctor_get(v_toCold_2584_, 11);
if (v_isRecordingDeps_2589_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = l_Lean_Elab_async;
lean_inc_ref(v_options_2592_);
v___x_2637_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_options_2592_, v___x_2636_, v_isRecordingDeps_2589_);
v___y_2627_ = v___x_2637_;
goto v___jp_2626_;
}
else
{
lean_object* v___x_2638_; 
lean_inc_ref(v_options_2592_);
v___x_2638_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_2592_);
v___y_2627_ = v___x_2638_;
goto v___jp_2626_;
}
v___jp_2516_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2535_ = l_Lean_maxRecDepth;
v___x_2536_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v___y_2518_, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2537_, 0, v_fileName_2519_);
lean_ctor_set(v___x_2537_, 1, v_fileMap_2520_);
lean_ctor_set(v___x_2537_, 2, v___y_2518_);
lean_ctor_set(v___x_2537_, 3, v___x_2536_);
lean_ctor_set(v___x_2537_, 4, v_currNamespace_2521_);
lean_ctor_set(v___x_2537_, 5, v_openDecls_2522_);
lean_ctor_set(v___x_2537_, 6, v_initHeartbeats_2523_);
lean_ctor_set(v___x_2537_, 7, v_maxHeartbeats_2524_);
lean_ctor_set(v___x_2537_, 8, v_quotContext_2525_);
lean_ctor_set(v___x_2537_, 9, v_currMacroScope_2526_);
lean_ctor_set(v___x_2537_, 10, v_cancelTk_x3f_2527_);
lean_ctor_set(v___x_2537_, 11, v_inheritedTraceOptions_2528_);
lean_inc(v_ref_2530_);
lean_inc(v_currRecDepth_2529_);
v___x_2538_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v_currRecDepth_2529_);
lean_ctor_set(v___x_2538_, 2, v_ref_2530_);
lean_ctor_set_uint16(v___x_2538_, sizeof(void*)*3, v___y_2517_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*3 + 2, v_suppressElabErrors_2531_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*3 + 3, v_checkDeprecated_2532_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*3 + 4, v_isRecordingDeps_2533_);
lean_inc_ref(v_expectedType_2490_);
lean_inc(v___x_2510_);
v___x_2539_ = l_Lean_Meta_mkAuxLemma(v___x_2510_, v_expectedType_2490_, v_a_2500_, v___x_2511_, v___x_2512_, v___x_2513_, v___x_2513_, v___x_2513_, v_a_2494_, v_a_2495_, v___x_2538_, v___y_2534_);
lean_dec_ref_known(v___x_2538_, 3);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2515_);
lean_dec_ref(v___x_2505_);
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2549_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2549_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2544_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(v___x_2510_, v___x_2509_);
v___x_2545_ = l_Lean_mkConst(v_a_2540_, v___x_2544_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2545_);
v___x_2547_ = v___x_2542_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v___x_2510_);
v_a_2550_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2552_ = v___x_2539_;
v_isShared_2553_ = v_isSharedCheck_2583_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2539_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2583_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v___x_2554_; 
v___x_2554_ = l_Lean_Exception_isInterrupt(v_a_2550_);
if (v___x_2554_ == 0)
{
uint8_t v___x_2555_; 
lean_inc(v_a_2550_);
v___x_2555_ = l_Lean_Exception_isRuntime(v_a_2550_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
lean_del_object(v___x_2552_);
v___x_2556_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2515_, v___x_2555_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref_known(v___x_2556_, 1);
v___x_2557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0));
v___x_2558_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5);
lean_inc_ref_n(v_expectedType_2490_, 2);
v___x_2559_ = l_Lean_mkAppB(v___x_2558_, v_expectedType_2490_, v___x_2505_);
v___x_2560_ = 1;
v___x_2561_ = lean_box(v___x_2513_);
v___x_2562_ = lean_box(v___x_2560_);
v___f_2563_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2563_, 0, v_a_2550_);
lean_closure_set(v___f_2563_, 1, v_tacticName_2489_);
lean_closure_set(v___f_2563_, 2, v_expectedType_2490_);
lean_closure_set(v___f_2563_, 3, v___x_2559_);
lean_closure_set(v___f_2563_, 4, v___x_2557_);
lean_closure_set(v___f_2563_, 5, v___x_2561_);
lean_closure_set(v___f_2563_, 6, v___x_2562_);
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = lean_mk_empty_array_with_capacity(v___x_2564_);
v___x_2566_ = lean_array_push(v___x_2565_, v_expectedType_2490_);
v___x_2567_ = l_Lean_MessageData_ofLazyM(v___f_2563_, v___x_2566_);
v___x_2568_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2567_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2550_);
lean_dec_ref(v___x_2505_);
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
v_a_2569_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2556_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2556_);
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
else
{
lean_object* v___x_2578_; 
lean_dec(v_a_2515_);
lean_dec_ref(v___x_2505_);
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
if (v_isShared_2553_ == 0)
{
v___x_2578_ = v___x_2552_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2550_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
lean_object* v___x_2581_; 
lean_dec(v_a_2515_);
lean_dec_ref(v___x_2505_);
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
if (v_isShared_2553_ == 0)
{
v___x_2581_ = v___x_2552_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2550_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
v___jp_2601_:
{
lean_object* v___x_2605_; lean_object* v_env_2606_; lean_object* v_nextMacroScope_2607_; lean_object* v_ngen_2608_; lean_object* v_auxDeclNGen_2609_; lean_object* v_traceState_2610_; lean_object* v_recordedDeps_2611_; lean_object* v_messages_2612_; lean_object* v_infoState_2613_; lean_object* v_snapshotTasks_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2624_; 
v___x_2605_ = lean_st_ref_take(v_a_2497_);
v_env_2606_ = lean_ctor_get(v___x_2605_, 0);
v_nextMacroScope_2607_ = lean_ctor_get(v___x_2605_, 1);
v_ngen_2608_ = lean_ctor_get(v___x_2605_, 2);
v_auxDeclNGen_2609_ = lean_ctor_get(v___x_2605_, 3);
v_traceState_2610_ = lean_ctor_get(v___x_2605_, 4);
v_recordedDeps_2611_ = lean_ctor_get(v___x_2605_, 6);
v_messages_2612_ = lean_ctor_get(v___x_2605_, 7);
v_infoState_2613_ = lean_ctor_get(v___x_2605_, 8);
v_snapshotTasks_2614_ = lean_ctor_get(v___x_2605_, 9);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2605_, 5);
lean_dec(v_unused_2625_);
v___x_2616_ = v___x_2605_;
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snapshotTasks_2614_);
lean_inc(v_infoState_2613_);
lean_inc(v_messages_2612_);
lean_inc(v_recordedDeps_2611_);
lean_inc(v_traceState_2610_);
lean_inc(v_auxDeclNGen_2609_);
lean_inc(v_ngen_2608_);
lean_inc(v_nextMacroScope_2607_);
lean_inc(v_env_2606_);
lean_dec(v___x_2605_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = l_Lean_Kernel_enableDiag(v_env_2606_, v___y_2604_);
v___x_2619_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 5, v___x_2619_);
lean_ctor_set(v___x_2616_, 0, v___x_2618_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_nextMacroScope_2607_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_ngen_2608_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_auxDeclNGen_2609_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v_traceState_2610_);
lean_ctor_set(v_reuseFailAlloc_2623_, 5, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2623_, 6, v_recordedDeps_2611_);
lean_ctor_set(v_reuseFailAlloc_2623_, 7, v_messages_2612_);
lean_ctor_set(v_reuseFailAlloc_2623_, 8, v_infoState_2613_);
lean_ctor_set(v_reuseFailAlloc_2623_, 9, v_snapshotTasks_2614_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_st_ref_put(v_a_2497_, v___x_2621_);
lean_inc_ref(v_inheritedTraceOptions_2600_);
lean_inc(v_cancelTk_x3f_2599_);
lean_inc(v_currMacroScope_2598_);
lean_inc(v_quotContext_2597_);
lean_inc(v_maxHeartbeats_2596_);
lean_inc(v_initHeartbeats_2595_);
lean_inc(v_openDecls_2594_);
lean_inc(v_currNamespace_2593_);
lean_inc_ref(v_fileMap_2591_);
lean_inc_ref(v_fileName_2590_);
v___y_2517_ = v___y_2602_;
v___y_2518_ = v___y_2603_;
v_fileName_2519_ = v_fileName_2590_;
v_fileMap_2520_ = v_fileMap_2591_;
v_currNamespace_2521_ = v_currNamespace_2593_;
v_openDecls_2522_ = v_openDecls_2594_;
v_initHeartbeats_2523_ = v_initHeartbeats_2595_;
v_maxHeartbeats_2524_ = v_maxHeartbeats_2596_;
v_quotContext_2525_ = v_quotContext_2597_;
v_currMacroScope_2526_ = v_currMacroScope_2598_;
v_cancelTk_x3f_2527_ = v_cancelTk_x3f_2599_;
v_inheritedTraceOptions_2528_ = v_inheritedTraceOptions_2600_;
v_currRecDepth_2529_ = v_currRecDepth_2585_;
v_ref_2530_ = v_ref_2586_;
v_suppressElabErrors_2531_ = v_suppressElabErrors_2587_;
v_checkDeprecated_2532_ = v_checkDeprecated_2588_;
v_isRecordingDeps_2533_ = v_isRecordingDeps_2589_;
v___y_2534_ = v_a_2497_;
goto v___jp_2516_;
}
}
}
v___jp_2626_:
{
uint16_t v___x_2628_; lean_object* v___x_2629_; lean_object* v_env_2630_; uint8_t v___x_2631_; uint16_t v___x_2632_; uint16_t v___x_2633_; uint16_t v___x_2634_; uint8_t v___x_2635_; 
v___x_2628_ = l_Lean_OptionFlags_ofOptions(v___y_2627_);
v___x_2629_ = lean_st_ref_get(v_a_2497_);
v_env_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_ref(v_env_2630_);
lean_dec(v___x_2629_);
v___x_2631_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2630_);
lean_dec_ref(v_env_2630_);
v___x_2632_ = 512;
v___x_2633_ = lean_uint16_land(v___x_2628_, v___x_2632_);
v___x_2634_ = 0;
v___x_2635_ = lean_uint16_dec_eq(v___x_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
if (v___x_2631_ == 0)
{
v___y_2602_ = v___x_2628_;
v___y_2603_ = v___y_2627_;
v___y_2604_ = v___x_2512_;
goto v___jp_2601_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2600_);
lean_inc(v_cancelTk_x3f_2599_);
lean_inc(v_currMacroScope_2598_);
lean_inc(v_quotContext_2597_);
lean_inc(v_maxHeartbeats_2596_);
lean_inc(v_initHeartbeats_2595_);
lean_inc(v_openDecls_2594_);
lean_inc(v_currNamespace_2593_);
lean_inc_ref(v_fileMap_2591_);
lean_inc_ref(v_fileName_2590_);
v___y_2517_ = v___x_2628_;
v___y_2518_ = v___y_2627_;
v_fileName_2519_ = v_fileName_2590_;
v_fileMap_2520_ = v_fileMap_2591_;
v_currNamespace_2521_ = v_currNamespace_2593_;
v_openDecls_2522_ = v_openDecls_2594_;
v_initHeartbeats_2523_ = v_initHeartbeats_2595_;
v_maxHeartbeats_2524_ = v_maxHeartbeats_2596_;
v_quotContext_2525_ = v_quotContext_2597_;
v_currMacroScope_2526_ = v_currMacroScope_2598_;
v_cancelTk_x3f_2527_ = v_cancelTk_x3f_2599_;
v_inheritedTraceOptions_2528_ = v_inheritedTraceOptions_2600_;
v_currRecDepth_2529_ = v_currRecDepth_2585_;
v_ref_2530_ = v_ref_2586_;
v_suppressElabErrors_2531_ = v_suppressElabErrors_2587_;
v_checkDeprecated_2532_ = v_checkDeprecated_2588_;
v_isRecordingDeps_2533_ = v_isRecordingDeps_2589_;
v___y_2534_ = v_a_2497_;
goto v___jp_2516_;
}
}
else
{
if (v___x_2631_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2600_);
lean_inc(v_cancelTk_x3f_2599_);
lean_inc(v_currMacroScope_2598_);
lean_inc(v_quotContext_2597_);
lean_inc(v_maxHeartbeats_2596_);
lean_inc(v_initHeartbeats_2595_);
lean_inc(v_openDecls_2594_);
lean_inc(v_currNamespace_2593_);
lean_inc_ref(v_fileMap_2591_);
lean_inc_ref(v_fileName_2590_);
v___y_2517_ = v___x_2628_;
v___y_2518_ = v___y_2627_;
v_fileName_2519_ = v_fileName_2590_;
v_fileMap_2520_ = v_fileMap_2591_;
v_currNamespace_2521_ = v_currNamespace_2593_;
v_openDecls_2522_ = v_openDecls_2594_;
v_initHeartbeats_2523_ = v_initHeartbeats_2595_;
v_maxHeartbeats_2524_ = v_maxHeartbeats_2596_;
v_quotContext_2525_ = v_quotContext_2597_;
v_currMacroScope_2526_ = v_currMacroScope_2598_;
v_cancelTk_x3f_2527_ = v_cancelTk_x3f_2599_;
v_inheritedTraceOptions_2528_ = v_inheritedTraceOptions_2600_;
v_currRecDepth_2529_ = v_currRecDepth_2585_;
v_ref_2530_ = v_ref_2586_;
v_suppressElabErrors_2531_ = v_suppressElabErrors_2587_;
v_checkDeprecated_2532_ = v_checkDeprecated_2588_;
v_isRecordingDeps_2533_ = v_isRecordingDeps_2589_;
v___y_2534_ = v_a_2497_;
goto v___jp_2516_;
}
else
{
v___y_2602_ = v___x_2628_;
v___y_2603_ = v___y_2627_;
v___y_2604_ = v___x_2513_;
goto v___jp_2601_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v___x_2510_);
lean_dec_ref(v___x_2505_);
lean_dec(v_a_2500_);
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
v_a_2639_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2514_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2514_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___x_2505_);
lean_dec_ref(v_params_2503_);
lean_dec(v_a_2500_);
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
v_a_2647_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2506_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2506_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2490_);
lean_dec(v_tacticName_2489_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object* v_tacticName_2655_, lean_object* v_expectedType_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2655_, v_expectedType_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* v_tacticName_2666_, lean_object* v_expectedType_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2666_, v_expectedType_2667_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* v_tacticName_2678_, lean_object* v_expectedType_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(v_tacticName_2678_, v_expectedType_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0));
v___x_2692_ = l_Lean_stringToMessageData(v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t v_native_2693_, uint8_t v_kernel_2694_, lean_object* v_tacticName_2695_, lean_object* v_expectedType_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; 
if (v_kernel_2694_ == 0)
{
v___y_2708_ = v___y_2698_;
v___y_2709_ = v___y_2699_;
v___y_2710_ = v___y_2700_;
v___y_2711_ = v___y_2701_;
v___y_2712_ = v___y_2702_;
v___y_2713_ = v___y_2703_;
v___y_2714_ = v___y_2704_;
v___y_2715_ = v___y_2705_;
goto v___jp_2707_;
}
else
{
if (v_native_2693_ == 0)
{
v___y_2708_ = v___y_2698_;
v___y_2709_ = v___y_2699_;
v___y_2710_ = v___y_2700_;
v___y_2711_ = v___y_2701_;
v___y_2712_ = v___y_2702_;
v___y_2713_ = v___y_2703_;
v___y_2714_ = v___y_2704_;
v___y_2715_ = v___y_2705_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_expectedType_2696_);
v___x_2723_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2724_ = l_Lean_MessageData_ofName(v_tacticName_2695_);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_obj_once(&l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1, &l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2725_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2727_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2728_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
v___jp_2707_:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_2696_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2716_) == 0)
{
if (v_native_2693_ == 0)
{
if (v_kernel_2694_ == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2695_, v_a_2717_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2718_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2720_; 
v_a_2719_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2720_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2695_, v_a_2719_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2720_;
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2722_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_2695_, v_a_2721_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2722_;
}
}
else
{
lean_dec(v_tacticName_2695_);
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object* v_native_2737_, lean_object* v_kernel_2738_, lean_object* v_tacticName_2739_, lean_object* v_expectedType_2740_, lean_object* v_x_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
uint8_t v_native_boxed_2751_; uint8_t v_kernel_boxed_2752_; lean_object* v_res_2753_; 
v_native_boxed_2751_ = lean_unbox(v_native_2737_);
v_kernel_boxed_2752_ = lean_unbox(v_kernel_2738_);
v_res_2753_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0(v_native_boxed_2751_, v_kernel_boxed_2752_, v_tacticName_2739_, v_expectedType_2740_, v_x_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v_x_2741_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t v_revert_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2756_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2767_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_a_2765_, v___x_2766_, v_revert_2754_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc_n(v_a_2768_, 2);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = l_Lean_MVarId_getDecl(v_a_2768_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v_lctx_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v_lctx_2771_ = lean_ctor_get(v_a_2770_, 1);
lean_inc_ref(v_lctx_2771_);
lean_dec(v_a_2770_);
v___x_2772_ = l_Lean_LocalContext_getFVarIds(v_lctx_2771_);
lean_dec_ref(v_lctx_2771_);
v___x_2773_ = 0;
v___x_2774_ = l_Lean_MVarId_revert(v_a_2768_, v___x_2772_, v___x_2773_, v_revert_2754_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v_snd_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2785_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v_snd_2776_ = lean_ctor_get(v_a_2775_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_a_2775_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_a_2775_, 0);
lean_dec(v_unused_2786_);
v___x_2778_ = v_a_2775_;
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_snd_2776_);
lean_dec(v_a_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 1);
lean_ctor_set(v___x_2778_, 1, v___x_2780_);
lean_ctor_set(v___x_2778_, 0, v_snd_2776_);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_snd_2776_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2782_, v___y_2756_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2783_;
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2787_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2774_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2774_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2768_);
v_a_2795_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2769_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2769_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
v_a_2803_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2767_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2767_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v_a_2811_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2764_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2764_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object* v_revert_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v_revert_boxed_2829_; lean_object* v_res_2830_; 
v_revert_boxed_2829_ = lean_unbox(v_revert_2819_);
v_res_2830_ = l_Lean_Elab_Tactic_evalDecideCore___lam__1(v_revert_boxed_2829_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* v_tacticName_2831_, lean_object* v_cfg_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
uint8_t v_kernel_2842_; uint8_t v_native_2843_; uint8_t v_revert_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; 
v_kernel_2842_ = lean_ctor_get_uint8(v_cfg_2832_, 0);
v_native_2843_ = lean_ctor_get_uint8(v_cfg_2832_, 1);
v_revert_2844_ = lean_ctor_get_uint8(v_cfg_2832_, 3);
v___x_2845_ = lean_box(v_native_2843_);
v___x_2846_ = lean_box(v_kernel_2842_);
lean_inc(v_tacticName_2831_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2847_, 0, v___x_2845_);
lean_closure_set(v___f_2847_, 1, v___x_2846_);
lean_closure_set(v___f_2847_, 2, v_tacticName_2831_);
if (v_revert_2844_ == 0)
{
v___y_2849_ = v_a_2833_;
v___y_2850_ = v_a_2834_;
v___y_2851_ = v_a_2835_;
v___y_2852_ = v_a_2836_;
v___y_2853_ = v_a_2837_;
v___y_2854_ = v_a_2838_;
v___y_2855_ = v_a_2839_;
v___y_2856_ = v_a_2840_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_box(v_revert_2844_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2860_, 0, v___x_2859_);
v___x_2861_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2860_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_dec_ref_known(v___x_2861_, 1);
v___y_2849_ = v_a_2833_;
v___y_2850_ = v_a_2834_;
v___y_2851_ = v_a_2835_;
v___y_2852_ = v_a_2836_;
v___y_2853_ = v_a_2837_;
v___y_2854_ = v_a_2838_;
v___y_2855_ = v_a_2839_;
v___y_2856_ = v_a_2840_;
goto v___jp_2848_;
}
else
{
lean_dec_ref(v___f_2847_);
lean_dec(v_tacticName_2831_);
return v___x_2861_;
}
}
v___jp_2848_:
{
uint8_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = 1;
v___x_2858_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacticName_2831_, v___f_2847_, v___x_2857_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v___x_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object* v_tacticName_2862_, lean_object* v_cfg_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Elab_Tactic_evalDecideCore(v_tacticName_2862_, v_cfg_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec_ref(v_cfg_2863_);
return v_res_2873_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_box(0);
v___x_2875_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(v_00_u03b1_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1));
v___x_2899_ = l_Lean_stringToMessageData(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(lean_object* v___x_2900_, lean_object* v_ctor_2901_, lean_object* v_args_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0));
v___x_2970_ = lean_string_dec_eq(v_ctor_2901_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_array_get_size(v_args_2902_);
v___x_2973_ = lean_unsigned_to_nat(4u);
v___x_2974_ = lean_nat_dec_eq(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
v___x_2975_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2);
v___x_2976_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v___x_2975_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2976_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2976_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
goto v___jp_2908_;
}
}
v___jp_2908_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = lean_array_get_borrowed(v___x_2900_, v_args_2902_, v___x_2909_);
lean_inc(v___x_2910_);
v___x_2911_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2910_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = lean_array_get_borrowed(v___x_2900_, v_args_2902_, v___x_2913_);
lean_inc(v___x_2914_);
v___x_2915_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2914_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = lean_unsigned_to_nat(2u);
v___x_2918_ = lean_array_get_borrowed(v___x_2900_, v_args_2902_, v___x_2917_);
lean_inc(v___x_2918_);
v___x_2919_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2918_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = lean_unsigned_to_nat(3u);
v___x_2922_ = lean_array_get_borrowed(v___x_2900_, v_args_2902_, v___x_2921_);
lean_inc(v___x_2922_);
v___x_2923_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2922_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2936_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2936_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2936_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; uint8_t v___x_2929_; uint8_t v___x_2930_; uint8_t v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2934_; 
v___x_2928_ = lean_alloc_ctor(0, 0, 4);
v___x_2929_ = lean_unbox(v_a_2912_);
lean_dec(v_a_2912_);
lean_ctor_set_uint8(v___x_2928_, 0, v___x_2929_);
v___x_2930_ = lean_unbox(v_a_2916_);
lean_dec(v_a_2916_);
lean_ctor_set_uint8(v___x_2928_, 1, v___x_2930_);
v___x_2931_ = lean_unbox(v_a_2920_);
lean_dec(v_a_2920_);
lean_ctor_set_uint8(v___x_2928_, 2, v___x_2931_);
v___x_2932_ = lean_unbox(v_a_2924_);
lean_dec(v_a_2924_);
lean_ctor_set_uint8(v___x_2928_, 3, v___x_2932_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2928_);
v___x_2934_ = v___x_2926_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2928_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_a_2920_);
lean_dec(v_a_2916_);
lean_dec(v_a_2912_);
v_a_2937_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2923_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2923_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_a_2916_);
lean_dec(v_a_2912_);
v_a_2945_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2919_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2919_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec(v_a_2912_);
v_a_2953_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2915_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2915_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v_a_2961_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2911_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2911_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed(lean_object* v___x_2985_, lean_object* v_ctor_2986_, lean_object* v_args_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(v___x_2985_, v_ctor_2986_, v_args_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_args_2987_);
lean_dec_ref(v_ctor_2986_);
lean_dec_ref(v___x_2985_);
return v_res_2993_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___f_2995_; 
v___x_2994_ = l_Lean_instInhabitedExpr;
v___f_2995_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2995_, 0, v___x_2994_);
return v___f_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___f_3011_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0);
v___x_3012_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3013_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_3012_, v___f_3011_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed(lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
return v_res_3020_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3024_ = l_Lean_Expr_const___override(v___x_3023_, v___x_3022_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
v___x_3028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0));
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
return v___x_3029_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig(void){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3);
return v___x_3030_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = lean_box(0);
v___x_3032_ = l_Lean_Elab_abortTermExceptionId;
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0);
v___x_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
return v_res_3038_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0));
v___x_3041_ = l_Lean_stringToMessageData(v___x_3040_);
return v___x_3041_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
v___x_3043_ = l_Lean_MessageData_ofExpr(v___x_3042_);
return v___x_3043_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2);
v___x_3045_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3);
v___x_3048_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3);
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3047_);
return v___x_3049_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5));
v___x_3052_ = l_Lean_stringToMessageData(v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_ty_x3f_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v_toCold_3070_; lean_object* v_currRecDepth_3071_; lean_object* v_ref_3072_; uint16_t v_optionFlags_3073_; uint8_t v_suppressElabErrors_3074_; uint8_t v_checkDeprecated_3075_; uint8_t v_isRecordingDeps_3076_; uint8_t v___x_3077_; lean_object* v_ref_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_ty_x3f_3064_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
v___x_3065_ = 1;
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_box(v___x_3065_);
v___x_3068_ = lean_box(v___x_3065_);
lean_inc(v_stx_3056_);
v___x_3069_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3069_, 0, v_stx_3056_);
lean_closure_set(v___x_3069_, 1, v_ty_x3f_3064_);
lean_closure_set(v___x_3069_, 2, v___x_3067_);
lean_closure_set(v___x_3069_, 3, v___x_3068_);
lean_closure_set(v___x_3069_, 4, v___x_3066_);
v_toCold_3070_ = lean_ctor_get(v_a_3061_, 0);
v_currRecDepth_3071_ = lean_ctor_get(v_a_3061_, 1);
v_ref_3072_ = lean_ctor_get(v_a_3061_, 2);
v_optionFlags_3073_ = lean_ctor_get_uint16(v_a_3061_, sizeof(void*)*3);
v_suppressElabErrors_3074_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*3 + 2);
v_checkDeprecated_3075_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3076_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*3 + 4);
v___x_3077_ = 1;
v_ref_3078_ = l_Lean_replaceRef(v_stx_3056_, v_ref_3072_);
lean_dec(v_stx_3056_);
lean_inc(v_currRecDepth_3071_);
lean_inc_ref(v_toCold_3070_);
v___x_3079_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3079_, 0, v_toCold_3070_);
lean_ctor_set(v___x_3079_, 1, v_currRecDepth_3071_);
lean_ctor_set(v___x_3079_, 2, v_ref_3078_);
lean_ctor_set_uint16(v___x_3079_, sizeof(void*)*3, v_optionFlags_3073_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3 + 2, v_suppressElabErrors_3074_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3 + 3, v_checkDeprecated_3075_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3 + 4, v_isRecordingDeps_3076_);
v___x_3080_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3069_, v___x_3077_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v___x_3079_, v_a_3062_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v_a_3083_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; uint8_t v___x_3167_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_a_3081_, v_a_3060_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3082_);
v___x_3167_ = l_Lean_Expr_hasSorry(v_a_3083_);
if (v___x_3167_ == 0)
{
v___y_3112_ = v_a_3057_;
v___y_3113_ = v_a_3058_;
v___y_3114_ = v_a_3059_;
v___y_3115_ = v_a_3060_;
v___y_3116_ = v___x_3079_;
v___y_3117_ = v_a_3062_;
goto v___jp_3111_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = l_Lean_Expr_hasSyntheticSorry(v_a_3083_);
if (v___x_3168_ == 0)
{
v___y_3149_ = v_a_3057_;
v___y_3150_ = v_a_3058_;
v___y_3151_ = v_a_3059_;
v___y_3152_ = v_a_3060_;
v___y_3153_ = v___x_3079_;
v___y_3154_ = v_a_3062_;
goto v___jp_3148_;
}
else
{
lean_object* v___x_3169_; lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_a_3083_);
lean_dec_ref_known(v___x_3079_, 3);
v___x_3169_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
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
v___jp_3084_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_3083_);
v___x_3092_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_3083_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_dec_ref(v___y_3089_);
lean_dec(v_a_3083_);
return v___x_3092_;
}
else
{
lean_object* v_a_3093_; uint8_t v___x_3094_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
v___x_3094_ = l_Lean_Exception_isInterrupt(v_a_3093_);
if (v___x_3094_ == 0)
{
uint8_t v___x_3095_; 
lean_inc(v_a_3093_);
v___x_3095_ = l_Lean_Exception_isRuntime(v_a_3093_);
if (v___x_3095_ == 0)
{
if (lean_obj_tag(v_a_3093_) == 0)
{
lean_dec_ref_known(v_a_3093_, 2);
lean_dec_ref(v___y_3089_);
lean_dec(v_a_3083_);
return v___x_3092_;
}
else
{
lean_object* v_id_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3109_; 
v_id_3096_ = lean_ctor_get(v_a_3093_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_a_3093_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v_a_3093_, 1);
lean_dec(v_unused_3110_);
v___x_3098_ = v_a_3093_;
v_isShared_3099_ = v_isSharedCheck_3109_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_id_3096_);
lean_dec(v_a_3093_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3109_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
uint8_t v___x_3100_; 
v___x_3100_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3091_, v_id_3096_);
lean_dec(v_id_3096_);
if (v___x_3100_ == 0)
{
lean_del_object(v___x_3098_);
lean_dec_ref(v___y_3089_);
lean_dec(v_a_3083_);
return v___x_3092_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
lean_dec_ref_known(v___x_3092_, 1);
v___x_3101_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4);
v___x_3102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6);
v___x_3103_ = l_Lean_indentExpr(v_a_3083_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set_tag(v___x_3098_, 7);
lean_ctor_set(v___x_3098_, 1, v___x_3103_);
lean_ctor_set(v___x_3098_, 0, v___x_3102_);
v___x_3105_ = v___x_3098_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3101_);
v___x_3107_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3106_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec_ref(v___y_3089_);
return v___x_3107_;
}
}
}
}
}
else
{
lean_dec(v_a_3093_);
lean_dec_ref(v___y_3089_);
lean_dec(v_a_3083_);
return v___x_3092_;
}
}
else
{
lean_dec(v_a_3093_);
lean_dec_ref(v___y_3089_);
lean_dec(v_a_3083_);
return v___x_3092_;
}
}
}
v___jp_3111_:
{
lean_object* v___x_3118_; 
lean_inc(v_a_3083_);
v___x_3118_ = l_Lean_Meta_getMVars(v_a_3083_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3120_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3120_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3119_, v___x_3066_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v_a_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; uint8_t v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = lean_unbox(v_a_3121_);
lean_dec(v_a_3121_);
if (v___x_3122_ == 0)
{
v___y_3085_ = v___y_3112_;
v___y_3086_ = v___y_3113_;
v___y_3087_ = v___y_3114_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3123_; lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v___y_3116_);
lean_dec(v_a_3083_);
v___x_3123_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___y_3116_);
lean_dec(v_a_3083_);
v_a_3132_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3120_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3120_);
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
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v___y_3116_);
lean_dec(v_a_3083_);
v_a_3140_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3118_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3118_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
v___jp_3148_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v___x_3155_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8);
v___x_3156_ = l_Lean_indentExpr(v_a_3083_);
v___x_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3157_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec_ref(v___y_3153_);
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
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref_known(v___x_3079_, 3);
v_a_3178_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3080_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3080_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_stx_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(lean_object* v_config_3226_, lean_object* v_item_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_item_3236_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3240_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3227_, v___x_3239_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3240_) == 0)
{
uint8_t v___x_3241_; 
lean_dec_ref_known(v___x_3240_, 1);
v___x_3241_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3227_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3242_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3227_);
lean_inc_ref(v_item_3227_);
v___x_3243_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3227_);
v___x_3244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_3245_ = lean_string_dec_eq(v___x_3242_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_3247_ = lean_string_dec_eq(v___x_3242_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_3249_ = lean_string_dec_eq(v___x_3242_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_3251_ = lean_string_dec_eq(v___x_3242_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; uint8_t v___x_3253_; 
v___x_3252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_3253_ = lean_string_dec_eq(v___x_3242_, v___x_3252_);
lean_dec_ref(v___x_3242_);
if (v___x_3253_ == 0)
{
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_item_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_3255_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3227_, v___x_3254_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3255_) == 0)
{
uint8_t v___x_3256_; 
lean_dec_ref_known(v___x_3255_, 1);
v___x_3256_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3243_);
if (v___x_3256_ == 0)
{
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_item_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3257_; 
lean_dec_ref(v___x_3243_);
v___x_3257_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3276_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3276_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3276_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
uint8_t v_kernel_3262_; uint8_t v_native_3263_; uint8_t v_revert_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3275_; 
v_kernel_3262_ = lean_ctor_get_uint8(v_config_3226_, 0);
v_native_3263_ = lean_ctor_get_uint8(v_config_3226_, 1);
v_revert_3264_ = lean_ctor_get_uint8(v_config_3226_, 3);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_config_3226_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3266_ = v_config_3226_;
v_isShared_3267_ = v_isSharedCheck_3275_;
goto v_resetjp_3265_;
}
else
{
lean_dec(v_config_3226_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3275_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 0, v_kernel_3262_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 1, v_native_3263_);
v___x_3269_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
uint8_t v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = lean_unbox(v_a_3258_);
lean_dec(v_a_3258_);
lean_ctor_set_uint8(v___x_3269_, 2, v___x_3270_);
lean_ctor_set_uint8(v___x_3269_, 3, v_revert_3264_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3269_);
v___x_3272_ = v___x_3260_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3269_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec_ref(v_config_3226_);
v_a_3277_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3257_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3257_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v___x_3243_);
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_a_3285_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3255_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3255_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec_ref(v___x_3242_);
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_3294_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3227_, v___x_3293_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3294_) == 0)
{
uint8_t v___x_3295_; 
lean_dec_ref_known(v___x_3294_, 1);
v___x_3295_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3243_);
if (v___x_3295_ == 0)
{
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_item_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3296_; 
lean_dec_ref(v___x_3243_);
v___x_3296_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3315_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3315_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3315_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
uint8_t v_kernel_3301_; uint8_t v_native_3302_; uint8_t v_zetaReduce_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3314_; 
v_kernel_3301_ = lean_ctor_get_uint8(v_config_3226_, 0);
v_native_3302_ = lean_ctor_get_uint8(v_config_3226_, 1);
v_zetaReduce_3303_ = lean_ctor_get_uint8(v_config_3226_, 2);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_config_3226_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3305_ = v_config_3226_;
v_isShared_3306_ = v_isSharedCheck_3314_;
goto v_resetjp_3304_;
}
else
{
lean_dec(v_config_3226_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3314_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3313_, 0, v_kernel_3301_);
lean_ctor_set_uint8(v_reuseFailAlloc_3313_, 1, v_native_3302_);
lean_ctor_set_uint8(v_reuseFailAlloc_3313_, 2, v_zetaReduce_3303_);
v___x_3308_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
uint8_t v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = lean_unbox(v_a_3297_);
lean_dec(v_a_3297_);
lean_ctor_set_uint8(v___x_3308_, 3, v___x_3309_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3308_);
v___x_3311_ = v___x_3299_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3308_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec_ref(v_config_3226_);
v_a_3316_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3296_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3296_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec_ref(v___x_3243_);
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_a_3324_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3294_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3294_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec_ref(v___x_3242_);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_3333_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3227_, v___x_3332_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3333_) == 0)
{
uint8_t v___x_3334_; 
lean_dec_ref_known(v___x_3333_, 1);
v___x_3334_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3243_);
if (v___x_3334_ == 0)
{
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_item_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3335_; 
lean_dec_ref(v___x_3243_);
v___x_3335_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3354_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3354_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3354_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
uint8_t v_kernel_3340_; uint8_t v_zetaReduce_3341_; uint8_t v_revert_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3353_; 
v_kernel_3340_ = lean_ctor_get_uint8(v_config_3226_, 0);
v_zetaReduce_3341_ = lean_ctor_get_uint8(v_config_3226_, 2);
v_revert_3342_ = lean_ctor_get_uint8(v_config_3226_, 3);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_config_3226_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3344_ = v_config_3226_;
v_isShared_3345_ = v_isSharedCheck_3353_;
goto v_resetjp_3343_;
}
else
{
lean_dec(v_config_3226_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3353_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3352_, 0, v_kernel_3340_);
v___x_3347_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
uint8_t v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_unbox(v_a_3336_);
lean_dec(v_a_3336_);
lean_ctor_set_uint8(v___x_3347_, 1, v___x_3348_);
lean_ctor_set_uint8(v___x_3347_, 2, v_zetaReduce_3341_);
lean_ctor_set_uint8(v___x_3347_, 3, v_revert_3342_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3347_);
v___x_3350_ = v___x_3338_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3347_);
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
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref(v_config_3226_);
v_a_3355_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3335_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3335_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref(v___x_3243_);
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_a_3363_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3333_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3333_);
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
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec_ref(v___x_3242_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_3372_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3227_, v___x_3371_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3372_) == 0)
{
uint8_t v___x_3373_; 
lean_dec_ref_known(v___x_3372_, 1);
v___x_3373_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3243_);
if (v___x_3373_ == 0)
{
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_item_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3374_; 
lean_dec_ref(v___x_3243_);
v___x_3374_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3393_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3393_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3393_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v_native_3379_; uint8_t v_zetaReduce_3380_; uint8_t v_revert_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3392_; 
v_native_3379_ = lean_ctor_get_uint8(v_config_3226_, 1);
v_zetaReduce_3380_ = lean_ctor_get_uint8(v_config_3226_, 2);
v_revert_3381_ = lean_ctor_get_uint8(v_config_3226_, 3);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_config_3226_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3383_ = v_config_3226_;
v_isShared_3384_ = v_isSharedCheck_3392_;
goto v_resetjp_3382_;
}
else
{
lean_dec(v_config_3226_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3392_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 0, 4);
v___x_3386_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
uint8_t v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = lean_unbox(v_a_3375_);
lean_dec(v_a_3375_);
lean_ctor_set_uint8(v___x_3386_, 0, v___x_3387_);
lean_ctor_set_uint8(v___x_3386_, 1, v_native_3379_);
lean_ctor_set_uint8(v___x_3386_, 2, v_zetaReduce_3380_);
lean_ctor_set_uint8(v___x_3386_, 3, v_revert_3381_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3386_);
v___x_3389_ = v___x_3377_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3386_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v_config_3226_);
v_a_3394_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3374_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3374_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___x_3243_);
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_a_3402_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3372_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3372_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
else
{
uint8_t v___x_3410_; 
lean_dec_ref(v___x_3242_);
lean_dec_ref(v_config_3226_);
v___x_3410_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3243_);
if (v___x_3410_ == 0)
{
lean_dec_ref(v_item_3227_);
v_item_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
lean_object* v_value_3411_; lean_object* v___x_3412_; 
lean_dec_ref(v___x_3243_);
v_value_3411_ = lean_ctor_get(v_item_3227_, 2);
lean_inc(v_value_3411_);
lean_dec_ref(v_item_3227_);
v___x_3412_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_value_3411_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
return v___x_3412_;
}
}
}
else
{
lean_dec_ref(v_config_3226_);
v_item_3236_ = v_item_3227_;
goto v___jp_3235_;
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v_item_3227_);
lean_dec_ref(v_config_3226_);
v_a_3413_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3240_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3240_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
v___jp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_3238_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3236_, v___x_3237_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3421_, lean_object* v_item_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(v_config_3421_, v_item_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_00_u03b1_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(v_00_u03b1_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
return v_res_3450_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3453_ = l_Lean_mkConst(v___x_3452_, v___x_3451_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0);
v___x_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(lean_object* v_cfg_3456_, lean_object* v_cfgItem_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1);
v___x_3466_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3456_, v_cfgItem_3457_, v___x_3465_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_3467_, lean_object* v_cfgItem_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(v_cfg_3467_, v_cfgItem_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v_cfgItem_3468_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object* v_cfg_3478_, lean_object* v_init_3479_, uint8_t v_logExceptions_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_onErr_3485_; lean_object* v_eval_3486_; 
v_onErr_3485_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0));
v_eval_3486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_3480_ == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3486_, v_init_3479_, v_cfg_3478_, v_onErr_3485_, v_logExceptions_3480_, v_a_3482_, v_a_3483_);
return v___x_3487_;
}
else
{
uint8_t v_recover_3488_; lean_object* v___x_3489_; 
v_recover_3488_ = lean_ctor_get_uint8(v_a_3481_, sizeof(void*)*1);
v___x_3489_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3486_, v_init_3479_, v_cfg_3478_, v_onErr_3485_, v_recover_3488_, v_a_3482_, v_a_3483_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object* v_cfg_3490_, lean_object* v_init_3491_, lean_object* v_logExceptions_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
uint8_t v_logExceptions_boxed_3497_; lean_object* v_res_3498_; 
v_logExceptions_boxed_3497_ = lean_unbox(v_logExceptions_3492_);
v_res_3498_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_cfg_3490_, v_init_3491_, v_logExceptions_boxed_3497_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec_ref(v_a_3493_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* v_cfg_3499_, lean_object* v_init_3500_, uint8_t v_logExceptions_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_cfg_3499_, v_init_3500_, v_logExceptions_3501_, v_a_3502_, v_a_3508_, v_a_3509_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* v_cfg_3512_, lean_object* v_init_3513_, lean_object* v_logExceptions_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
uint8_t v_logExceptions_boxed_3524_; lean_object* v_res_3525_; 
v_logExceptions_boxed_3524_ = lean_unbox(v_logExceptions_3514_);
v_res_3525_ = l_Lean_Elab_Tactic_elabDecideConfig(v_cfg_3512_, v_init_3513_, v_logExceptions_boxed_3524_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* v_stx_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = l_Lean_Syntax_getArg(v_stx_3531_, v___x_3541_);
v___x_3543_ = 1;
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__0));
v___x_3545_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3542_, v___x_3544_, v___x_3543_, v_a_3532_, v_a_3538_, v_a_3539_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__1));
v___x_3548_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3547_, v_a_3546_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3546_);
return v___x_3548_;
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
v_a_3549_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3545_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3545_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object* v_stx_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_Elab_Tactic_evalDecide(v_stx_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_stx_3557_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3581_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0));
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3584_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
v___x_3585_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3581_, v___x_3582_, v___x_3583_, v___x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6));
v___x_3616_ = l_Lean_addBuiltinDeclarationRanges(v___x_3614_, v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* v_stx_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = l_Lean_Syntax_getArg(v_stx_3622_, v___x_3632_);
v___x_3634_ = 1;
v___x_3635_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__0));
v___x_3636_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3633_, v___x_3635_, v___x_3634_, v_a_3623_, v_a_3629_, v_a_3630_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; uint8_t v_kernel_3638_; uint8_t v_zetaReduce_3639_; uint8_t v_revert_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3649_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v_kernel_3638_ = lean_ctor_get_uint8(v_a_3637_, 0);
v_zetaReduce_3639_ = lean_ctor_get_uint8(v_a_3637_, 2);
v_revert_3640_ = lean_ctor_get_uint8(v_a_3637_, 3);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_a_3637_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3642_ = v_a_3637_;
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v_a_3637_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3649_;
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
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, 0, v_kernel_3638_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, 2, v_zetaReduce_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, 3, v_revert_3640_);
v___x_3645_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_ctor_set_uint8(v___x_3645_, 1, v___x_3634_);
v___x_3646_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___closed__1));
v___x_3647_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3646_, v___x_3645_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
lean_dec_ref(v___x_3645_);
return v___x_3647_;
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
v_a_3650_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3636_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3636_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object* v_stx_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_Elab_Tactic_evalNativeDecide(v_stx_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_stx_3658_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3682_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1));
v___x_3684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3685_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
v___x_3686_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3682_, v___x_3683_, v___x_3684_, v___x_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6));
v___x_3717_ = l_Lean_addBuiltinDeclarationRanges(v___x_3715_, v___x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object* v_a_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
return v_res_3719_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Decide(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig = _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig);
res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Decide(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Native(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Decide(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Decide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Decide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Decide(builtin);
}
#ifdef __cplusplus
}
#endif
