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
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
lean_object* l_Lean_Elab_Term_getLevelNames___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(196, 237, 71, 156, 244, 3, 80, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__10_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 96, 18, 10, 225, 62, 78, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_value;
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
lean_object* v_options_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_options_104_ = lean_ctor_get(v___y_102_, 2);
v___x_105_ = l_Lean_Elab_pp_macroStack;
v___x_106_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v_options_104_, v___x_105_);
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
lean_object* v___x_138_; lean_object* v_env_139_; lean_object* v___x_140_; lean_object* v_mctx_141_; lean_object* v_lctx_142_; lean_object* v_options_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v___x_140_ = lean_st_ref_get(v___y_134_);
v_mctx_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_mctx_141_);
lean_dec(v___x_140_);
v_lctx_142_ = lean_ctor_get(v___y_133_, 2);
v_options_143_ = lean_ctor_get(v___y_135_, 2);
lean_inc_ref(v_options_143_);
lean_inc_ref(v_lctx_142_);
v___x_144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_144_, 0, v_env_139_);
lean_ctor_set(v___x_144_, 1, v_mctx_141_);
lean_ctor_set(v___x_144_, 2, v_lctx_142_);
lean_ctor_set(v___x_144_, 3, v_options_143_);
v___x_145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_msgData_132_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0___boxed(lean_object* v_msgData_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msgData_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_ref_162_; lean_object* v___x_163_; lean_object* v_a_164_; lean_object* v_macroStack_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_ref_162_ = lean_ctor_get(v___y_159_, 5);
v___x_163_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_154_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref(v___x_163_);
v_macroStack_165_ = lean_ctor_get(v___y_155_, 1);
v___x_166_ = l_Lean_Elab_getBetterRef(v_ref_162_, v_macroStack_165_);
lean_inc(v_macroStack_165_);
v___x_167_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_a_164_, v_macroStack_165_, v___y_159_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_176_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_166_);
lean_ctor_set(v___x_172_, 1, v_a_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 1);
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg___boxed(lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_185_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2));
v___x_191_ = l_Lean_stringToMessageData(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3);
v___x_193_ = l_Lean_MessageData_hint_x27(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object* v_expectedType_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v_expectedType_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___x_250_; lean_object* v_a_251_; uint8_t v___x_252_; 
v___x_250_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_expectedType_197_, v_a_201_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_250_);
v___x_252_ = l_Lean_Expr_hasFVar(v_a_251_);
if (v___x_252_ == 0)
{
v_expectedType_230_ = v_a_251_;
v___y_231_ = v_a_198_;
v___y_232_ = v_a_199_;
v___y_233_ = v_a_200_;
v___y_234_ = v_a_201_;
v___y_235_ = v_a_202_;
v___y_236_ = v_a_203_;
goto v___jp_229_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Meta_zetaReduce(v_a_251_, v___x_252_, v___x_252_, v___x_252_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v_expectedType_230_ = v_a_254_;
v___y_231_ = v_a_198_;
v___y_232_ = v_a_199_;
v___y_233_ = v_a_200_;
v___y_234_ = v_a_201_;
v___y_235_ = v_a_202_;
v___y_236_ = v_a_203_;
goto v___jp_229_;
}
else
{
return v___x_253_;
}
}
v___jp_205_:
{
uint8_t v___x_213_; 
v___x_213_ = l_Lean_Expr_hasFVar(v___y_206_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___y_206_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v___x_215_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1);
v___x_216_ = l_Lean_indentExpr(v___y_206_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_219_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
v___jp_229_:
{
uint8_t v___x_237_; 
v___x_237_ = l_Lean_Expr_hasMVar(v_expectedType_230_);
if (v___x_237_ == 0)
{
v___y_206_ = v_expectedType_230_;
v___y_207_ = v___y_231_;
v___y_208_ = v___y_232_;
v___y_209_ = v___y_233_;
v___y_210_ = v___y_234_;
v___y_211_ = v___y_235_;
v___y_212_ = v___y_236_;
goto v___jp_205_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v___x_238_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6);
v___x_239_ = l_Lean_indentExpr(v_expectedType_230_);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_240_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(lean_object* v_expectedType_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(lean_object* v_00_u03b1_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___boxed(lean_object* v_00_u03b1_274_, lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(v_00_u03b1_274_, v_msg_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(lean_object* v_msgData_284_, lean_object* v_macroStack_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_284_, v_macroStack_285_, v___y_290_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___boxed(lean_object* v_msgData_294_, lean_object* v_macroStack_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(v_msgData_294_, v_macroStack_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(lean_object* v_declName_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_env_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v___x_309_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_308_, v_declName_304_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(lean_object* v_declName_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_311_, v___y_312_);
lean_dec(v___y_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(lean_object* v_declName_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_315_, v___y_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(lean_object* v_declName_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(v_declName_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_328_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = l_Lean_maxRecDepthErrorMessage;
v___x_335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3);
v___x_337_ = l_Lean_MessageData_ofFormat(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4);
v___x_339_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_340_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object* v_ref_341_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_ref_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object* v_ref_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object* v_00_u03b1_349_, lean_object* v_ref_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_350_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object* v_00_u03b1_357_, lean_object* v_ref_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(v_00_u03b1_357_, v_ref_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_364_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0(void){
_start:
{
lean_object* v___x_394_; lean_object* v_dummy_395_; 
v___x_394_ = lean_box(0);
v_dummy_395_ = l_Lean_Expr_sort___override(v___x_394_);
return v_dummy_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* v_expr_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v_fileName_506_; lean_object* v_fileMap_507_; lean_object* v_options_508_; lean_object* v_currRecDepth_509_; lean_object* v_maxRecDepth_510_; lean_object* v_ref_511_; lean_object* v_currNamespace_512_; lean_object* v_openDecls_513_; lean_object* v_initHeartbeats_514_; lean_object* v_maxHeartbeats_515_; lean_object* v_quotContext_516_; lean_object* v_currMacroScope_517_; uint8_t v_diag_518_; lean_object* v_cancelTk_x3f_519_; uint8_t v_suppressElabErrors_520_; lean_object* v_inheritedTraceOptions_521_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_fileName_506_ = lean_ctor_get(v_a_406_, 0);
lean_inc_ref(v_fileName_506_);
v_fileMap_507_ = lean_ctor_get(v_a_406_, 1);
lean_inc_ref(v_fileMap_507_);
v_options_508_ = lean_ctor_get(v_a_406_, 2);
lean_inc_ref(v_options_508_);
v_currRecDepth_509_ = lean_ctor_get(v_a_406_, 3);
lean_inc(v_currRecDepth_509_);
v_maxRecDepth_510_ = lean_ctor_get(v_a_406_, 4);
lean_inc(v_maxRecDepth_510_);
v_ref_511_ = lean_ctor_get(v_a_406_, 5);
lean_inc(v_ref_511_);
v_currNamespace_512_ = lean_ctor_get(v_a_406_, 6);
lean_inc(v_currNamespace_512_);
v_openDecls_513_ = lean_ctor_get(v_a_406_, 7);
lean_inc(v_openDecls_513_);
v_initHeartbeats_514_ = lean_ctor_get(v_a_406_, 8);
lean_inc(v_initHeartbeats_514_);
v_maxHeartbeats_515_ = lean_ctor_get(v_a_406_, 9);
lean_inc(v_maxHeartbeats_515_);
v_quotContext_516_ = lean_ctor_get(v_a_406_, 10);
lean_inc(v_quotContext_516_);
v_currMacroScope_517_ = lean_ctor_get(v_a_406_, 11);
lean_inc(v_currMacroScope_517_);
v_diag_518_ = lean_ctor_get_uint8(v_a_406_, sizeof(void*)*14);
v_cancelTk_x3f_519_ = lean_ctor_get(v_a_406_, 12);
lean_inc(v_cancelTk_x3f_519_);
v_suppressElabErrors_520_ = lean_ctor_get_uint8(v_a_406_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_521_ = lean_ctor_get(v_a_406_, 13);
lean_inc_ref(v_inheritedTraceOptions_521_);
lean_dec_ref(v_a_406_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_nat_dec_eq(v_maxRecDepth_510_, v___x_549_);
if (v___x_550_ == 0)
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_eq(v_currRecDepth_509_, v_maxRecDepth_510_);
if (v___x_551_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v___x_552_; 
lean_dec_ref(v_inheritedTraceOptions_521_);
lean_dec(v_cancelTk_x3f_519_);
lean_dec(v_currMacroScope_517_);
lean_dec(v_quotContext_516_);
lean_dec(v_maxHeartbeats_515_);
lean_dec(v_initHeartbeats_514_);
lean_dec(v_openDecls_513_);
lean_dec(v_currNamespace_512_);
lean_dec(v_maxRecDepth_510_);
lean_dec(v_currRecDepth_509_);
lean_dec_ref(v_options_508_);
lean_dec_ref(v_fileMap_507_);
lean_dec_ref(v_fileName_506_);
lean_dec_ref(v_expr_403_);
v___x_552_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_511_);
return v___x_552_;
}
}
else
{
goto v___jp_522_;
}
v___jp_409_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = lean_nat_sub(v___y_410_, v___x_414_);
lean_dec(v___y_410_);
v___x_416_ = lean_nat_sub(v___x_415_, v___y_412_);
lean_dec(v___x_415_);
v___x_417_ = l_Lean_Expr_getRevArg_x21(v___y_411_, v___x_416_);
lean_dec_ref(v___y_411_);
v_expr_403_ = v___x_417_;
v_a_406_ = v___y_413_;
goto _start;
}
v___jp_419_:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Expr_getAppFn(v___y_421_);
if (lean_obj_tag(v___x_427_) == 4)
{
lean_object* v_declName_428_; lean_object* v___x_429_; 
v_declName_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_declName_428_);
lean_dec_ref_known(v___x_427_, 2);
v___x_429_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_428_, v___y_426_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_472_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_472_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_472_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_472_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
if (lean_obj_tag(v_a_430_) == 1)
{
lean_object* v_val_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_val_434_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v_a_430_, 1);
v___x_435_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_434_);
v___x_436_ = lean_nat_dec_le(v___x_435_, v___y_420_);
lean_dec(v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_438_; 
lean_dec(v_val_434_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_420_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___y_421_);
v___x_438_ = v___x_432_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___y_421_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v_numDiscrs_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_dummy_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_del_object(v___x_432_);
v_numDiscrs_440_ = lean_ctor_get(v_val_434_, 1);
lean_inc(v_numDiscrs_440_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0));
v_dummy_443_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0);
lean_inc(v___y_420_);
v___x_444_ = lean_mk_array(v___y_420_, v_dummy_443_);
v___x_445_ = lean_nat_sub(v___y_420_, v___y_422_);
lean_dec(v___y_420_);
lean_inc_ref(v___y_421_);
v___x_446_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_421_, v___x_444_, v___x_445_);
v___x_447_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_numDiscrs_440_, v_val_434_, v___x_446_, v___x_441_, v___x_442_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec_ref(v___x_446_);
lean_dec(v_val_434_);
lean_dec(v_numDiscrs_440_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_460_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_460_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_460_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_460_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_fst_452_; 
v_fst_452_ = lean_ctor_get(v_a_448_, 0);
lean_inc(v_fst_452_);
lean_dec(v_a_448_);
if (lean_obj_tag(v_fst_452_) == 0)
{
lean_object* v___x_454_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___y_421_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___y_421_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v_val_456_; lean_object* v___x_458_; 
lean_dec_ref(v___y_421_);
v_val_456_ = lean_ctor_get(v_fst_452_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v_fst_452_, 1);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_val_456_);
v___x_458_ = v___x_450_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_val_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v___y_421_);
v_a_461_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_447_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_447_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_a_430_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_420_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___y_421_);
v___x_470_ = v___x_432_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___y_421_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v___y_425_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
v_a_473_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_429_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_429_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
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
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v___x_481_; 
lean_dec_ref(v___x_427_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_420_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___y_421_);
return v___x_481_;
}
}
v___jp_482_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_490_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3));
v___x_491_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5));
v___x_492_ = lean_unsigned_to_nat(3u);
v___x_493_ = l_Lean_Expr_isAppOfArity(v___y_484_, v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
if (lean_obj_tag(v___y_484_) == 11)
{
lean_object* v_typeName_494_; 
v_typeName_494_ = lean_ctor_get(v___y_484_, 0);
if (lean_obj_tag(v_typeName_494_) == 1)
{
lean_object* v_pre_495_; 
v_pre_495_ = lean_ctor_get(v_typeName_494_, 0);
if (lean_obj_tag(v_pre_495_) == 0)
{
lean_object* v_idx_496_; lean_object* v_struct_497_; lean_object* v_str_498_; uint8_t v___x_499_; 
v_idx_496_ = lean_ctor_get(v___y_484_, 1);
v_struct_497_ = lean_ctor_get(v___y_484_, 2);
v_str_498_ = lean_ctor_get(v_typeName_494_, 1);
v___x_499_ = lean_string_dec_eq(v_str_498_, v___x_490_);
if (v___x_499_ == 0)
{
v___y_420_ = v___y_483_;
v___y_421_ = v___y_484_;
v___y_422_ = v___y_485_;
v___y_423_ = v___y_486_;
v___y_424_ = v___y_487_;
v___y_425_ = v___y_488_;
v___y_426_ = v___y_489_;
goto v___jp_419_;
}
else
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_nat_dec_eq(v_idx_496_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_420_ = v___y_483_;
v___y_421_ = v___y_484_;
v___y_422_ = v___y_485_;
v___y_423_ = v___y_486_;
v___y_424_ = v___y_487_;
v___y_425_ = v___y_488_;
v___y_426_ = v___y_489_;
goto v___jp_419_;
}
else
{
lean_inc_ref(v_struct_497_);
lean_dec_ref_known(v___y_484_, 3);
lean_dec(v___y_483_);
v_expr_403_ = v_struct_497_;
v_a_404_ = v___y_486_;
v_a_405_ = v___y_487_;
v_a_406_ = v___y_488_;
v_a_407_ = v___y_489_;
goto _start;
}
}
}
else
{
v___y_420_ = v___y_483_;
v___y_421_ = v___y_484_;
v___y_422_ = v___y_485_;
v___y_423_ = v___y_486_;
v___y_424_ = v___y_487_;
v___y_425_ = v___y_488_;
v___y_426_ = v___y_489_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v___y_483_;
v___y_421_ = v___y_484_;
v___y_422_ = v___y_485_;
v___y_423_ = v___y_486_;
v___y_424_ = v___y_487_;
v___y_425_ = v___y_488_;
v___y_426_ = v___y_489_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v___y_483_;
v___y_421_ = v___y_484_;
v___y_422_ = v___y_485_;
v___y_423_ = v___y_486_;
v___y_424_ = v___y_487_;
v___y_425_ = v___y_488_;
v___y_426_ = v___y_489_;
goto v___jp_419_;
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v___y_483_);
v___x_503_ = l_Lean_Expr_appFn_x21(v___y_484_);
lean_dec_ref(v___y_484_);
v___x_504_ = l_Lean_Expr_appArg_x21(v___x_503_);
lean_dec_ref(v___x_503_);
v_expr_403_ = v___x_504_;
v_a_404_ = v___y_486_;
v_a_405_ = v___y_487_;
v_a_406_ = v___y_488_;
v_a_407_ = v___y_489_;
goto _start;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_currRecDepth_509_, v___x_523_);
lean_dec(v_currRecDepth_509_);
v___x_525_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_525_, 0, v_fileName_506_);
lean_ctor_set(v___x_525_, 1, v_fileMap_507_);
lean_ctor_set(v___x_525_, 2, v_options_508_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
lean_ctor_set(v___x_525_, 4, v_maxRecDepth_510_);
lean_ctor_set(v___x_525_, 5, v_ref_511_);
lean_ctor_set(v___x_525_, 6, v_currNamespace_512_);
lean_ctor_set(v___x_525_, 7, v_openDecls_513_);
lean_ctor_set(v___x_525_, 8, v_initHeartbeats_514_);
lean_ctor_set(v___x_525_, 9, v_maxHeartbeats_515_);
lean_ctor_set(v___x_525_, 10, v_quotContext_516_);
lean_ctor_set(v___x_525_, 11, v_currMacroScope_517_);
lean_ctor_set(v___x_525_, 12, v_cancelTk_x3f_519_);
lean_ctor_set(v___x_525_, 13, v_inheritedTraceOptions_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*14, v_diag_518_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*14 + 1, v_suppressElabErrors_520_);
lean_inc(v_a_407_);
lean_inc_ref(v___x_525_);
lean_inc(v_a_405_);
lean_inc_ref(v_a_404_);
v___x_526_ = lean_whnf(v_expr_403_, v_a_404_, v_a_405_, v___x_525_, v_a_407_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v_env_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; uint8_t v___x_533_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = lean_st_ref_get(v_a_407_);
v_env_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_env_529_);
lean_dec(v___x_528_);
v___x_530_ = l_Lean_Expr_getAppNumArgs(v_a_527_);
v___x_531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5));
v___x_532_ = 1;
v___x_533_ = l_Lean_Environment_contains(v_env_529_, v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(5u);
v___x_535_ = lean_nat_dec_le(v___x_534_, v___x_530_);
if (v___x_535_ == 0)
{
v___y_483_ = v___x_530_;
v___y_484_ = v_a_527_;
v___y_485_ = v___x_523_;
v___y_486_ = v_a_404_;
v___y_487_ = v_a_405_;
v___y_488_ = v___x_525_;
v___y_489_ = v_a_407_;
goto v___jp_482_;
}
else
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2));
v___x_537_ = l_Lean_Expr_isAppOf(v_a_527_, v___x_536_);
if (v___x_537_ == 0)
{
v___y_483_ = v___x_530_;
v___y_484_ = v_a_527_;
v___y_485_ = v___x_523_;
v___y_486_ = v_a_404_;
v___y_487_ = v_a_405_;
v___y_488_ = v___x_525_;
v___y_489_ = v_a_407_;
goto v___jp_482_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(4u);
v___x_539_ = lean_nat_sub(v___x_530_, v___x_538_);
lean_dec(v___x_530_);
v___x_540_ = lean_nat_sub(v___x_539_, v___x_523_);
lean_dec(v___x_539_);
v___x_541_ = l_Lean_Expr_getRevArg_x21(v_a_527_, v___x_540_);
lean_dec(v_a_527_);
v_expr_403_ = v___x_541_;
v_a_406_ = v___x_525_;
goto _start;
}
}
}
else
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(4u);
v___x_544_ = lean_nat_dec_le(v___x_543_, v___x_530_);
if (v___x_544_ == 0)
{
v___y_483_ = v___x_530_;
v___y_484_ = v_a_527_;
v___y_485_ = v___x_523_;
v___y_486_ = v_a_404_;
v___y_487_ = v_a_405_;
v___y_488_ = v___x_525_;
v___y_489_ = v_a_407_;
goto v___jp_482_;
}
else
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3));
v___x_546_ = l_Lean_Expr_isAppOf(v_a_527_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2));
v___x_548_ = l_Lean_Expr_isAppOf(v_a_527_, v___x_547_);
if (v___x_548_ == 0)
{
v___y_483_ = v___x_530_;
v___y_484_ = v_a_527_;
v___y_485_ = v___x_523_;
v___y_486_ = v_a_404_;
v___y_487_ = v_a_405_;
v___y_488_ = v___x_525_;
v___y_489_ = v_a_407_;
goto v___jp_482_;
}
else
{
v___y_410_ = v___x_530_;
v___y_411_ = v_a_527_;
v___y_412_ = v___x_523_;
v___y_413_ = v___x_525_;
goto v___jp_409_;
}
}
else
{
v___y_410_ = v___x_530_;
v___y_411_ = v_a_527_;
v___y_412_ = v___x_523_;
v___y_413_ = v___x_525_;
goto v___jp_409_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_525_, 14);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(lean_object* v_upperBound_553_, lean_object* v_val_554_, lean_object* v___x_555_, lean_object* v_a_556_, lean_object* v_b_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_a_564_; uint8_t v___x_568_; 
v___x_568_ = lean_nat_dec_lt(v_a_556_, v_upperBound_553_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v_a_556_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v_b_557_);
return v___x_569_;
}
else
{
lean_object* v_numParams_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v_b_557_);
v_numParams_570_ = lean_ctor_get(v_val_554_, 0);
v___x_571_ = l_Lean_instInhabitedExpr;
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_numParams_570_, v___x_572_);
v___x_574_ = lean_nat_add(v___x_573_, v_a_556_);
lean_dec(v___x_573_);
v___x_575_ = lean_array_get_borrowed(v___x_571_, v___x_555_, v___x_574_);
lean_dec(v___x_574_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___x_575_);
v___x_576_ = lean_infer_type(v___x_575_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
v___x_578_ = lean_whnf(v_a_577_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = lean_box(0);
v___x_581_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0));
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2));
v___x_583_ = l_Lean_Expr_isConstOf(v_a_579_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5));
v___x_585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_586_ = l_Lean_Expr_isAppOf(v_a_579_, v___x_585_);
lean_dec(v_a_579_);
if (v___x_586_ == 0)
{
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
else
{
lean_object* v___x_587_; lean_object* v_env_588_; uint8_t v___x_589_; 
v___x_587_ = lean_st_ref_get(v___y_561_);
v_env_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_Environment_contains(v_env_588_, v___x_584_, v___x_586_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___x_575_);
v___x_590_ = lean_whnf(v___x_575_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_593_ = l_Lean_Expr_isAppOf(v_a_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__10));
v___x_595_ = l_Lean_Expr_isAppOf(v_a_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v_a_556_);
lean_inc_ref(v___y_560_);
v___x_596_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_591_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_606_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_a_597_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_580_);
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
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_596_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_596_);
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
else
{
lean_dec(v_a_591_);
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
}
else
{
lean_dec(v_a_591_);
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_a_556_);
v_a_615_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_590_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_590_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_575_);
v___x_624_ = l_Lean_Expr_proj___override(v___x_585_, v___x_623_, v___x_575_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
v___x_625_ = lean_whnf(v___x_624_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12));
v___x_628_ = l_Lean_Expr_isConstOf(v_a_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14));
v___x_630_ = l_Lean_Expr_isConstOf(v_a_626_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec(v_a_556_);
lean_inc_ref(v___y_560_);
v___x_631_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_626_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_641_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_641_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_641_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_641_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v_a_632_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_580_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_631_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_631_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_dec(v_a_626_);
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
}
else
{
lean_dec(v_a_626_);
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_a_556_);
v_a_650_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_625_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_625_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
else
{
lean_object* v___x_658_; 
lean_dec(v_a_579_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___x_575_);
v___x_658_ = lean_whnf(v___x_575_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12));
v___x_661_ = l_Lean_Expr_isConstOf(v_a_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14));
v___x_663_ = l_Lean_Expr_isConstOf(v_a_659_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v_a_556_);
lean_inc_ref(v___y_560_);
v___x_664_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_659_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_674_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_674_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_a_665_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_580_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_670_);
v___x_672_ = v___x_667_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_664_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_664_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_dec(v_a_659_);
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
}
else
{
lean_dec(v_a_659_);
v_a_564_ = v___x_581_;
goto v___jp_563_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_556_);
v_a_683_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_658_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_658_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_556_);
v_a_691_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_578_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_578_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
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
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_a_556_);
v_a_699_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_576_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_576_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_a_556_, v___x_565_);
lean_dec(v_a_556_);
lean_inc_ref(v_a_564_);
v_a_556_ = v___x_566_;
v_b_557_ = v_a_564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___boxed(lean_object* v_upperBound_707_, lean_object* v_val_708_, lean_object* v___x_709_, lean_object* v_a_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_upperBound_707_, v_val_708_, v___x_709_, v_a_710_, v_b_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v_val_708_);
lean_dec(v_upperBound_707_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object* v_expr_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_expr_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(lean_object* v_upperBound_725_, lean_object* v_val_726_, lean_object* v___x_727_, lean_object* v_inst_728_, lean_object* v_R_729_, lean_object* v_a_730_, lean_object* v_b_731_, lean_object* v_c_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_upperBound_725_, v_val_726_, v___x_727_, v_a_730_, v_b_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(lean_object* v_upperBound_739_, lean_object* v_val_740_, lean_object* v___x_741_, lean_object* v_inst_742_, lean_object* v_R_743_, lean_object* v_a_744_, lean_object* v_b_745_, lean_object* v_c_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_upperBound_739_, v_val_740_, v___x_741_, v_inst_742_, v_R_743_, v_a_744_, v_b_745_, v_c_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v_val_740_);
lean_dec(v_upperBound_739_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_ref_759_; lean_object* v___x_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_ref_759_ = lean_ctor_get(v___y_756_, 5);
v___x_760_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_769_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_inc(v_ref_759_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_ref_759_);
lean_ctor_set(v___x_765_, 1, v_a_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 1);
lean_ctor_set(v___x_763_, 0, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_box(0);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1));
v___x_782_ = l_Lean_mkConst(v___x_781_, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore(lean_object* v_tacticName_792_, lean_object* v_expectedType_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
lean_inc_ref(v_expectedType_793_);
v___x_803_ = l_Lean_Meta_mkDecide(v_expectedType_793_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_843_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_843_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_843_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_843_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_ref_808_; lean_object* v___x_810_; 
v_ref_808_ = lean_ctor_get(v_a_800_, 5);
lean_inc(v_ref_808_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 1);
lean_ctor_set(v___x_806_, 0, v_ref_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_ref_808_);
v___x_810_ = v_reuseFailAlloc_842_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; 
lean_inc(v_a_804_);
lean_inc(v_tacticName_792_);
v___x_811_ = l_Lean_Meta_nativeEqTrue(v_tacticName_792_, v_a_804_, v___x_810_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec_ref(v___x_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_833_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_833_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_833_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_833_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
if (lean_obj_tag(v_a_812_) == 0)
{
lean_object* v_prf_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v_tacticName_792_);
v_prf_816_ = lean_ctor_get(v_a_812_, 0);
lean_inc_ref(v_prf_816_);
lean_dec_ref_known(v_a_812_, 1);
v___x_817_ = l_Lean_Expr_appArg_x21(v_a_804_);
lean_dec(v_a_804_);
v___x_818_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_819_ = l_Lean_mkApp3(v___x_818_, v_expectedType_793_, v___x_817_, v_prf_816_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_821_ = v___x_814_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_814_);
lean_dec(v_a_804_);
v___x_823_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_824_ = l_Lean_MessageData_ofName(v_tacticName_792_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_indentExpr(v_expectedType_793_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_831_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
return v___x_832_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_a_804_);
lean_dec_ref(v_expectedType_793_);
lean_dec(v_tacticName_792_);
v_a_834_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_811_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_811_);
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
}
}
else
{
lean_dec_ref(v_expectedType_793_);
lean_dec(v_tacticName_792_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(lean_object* v_tacticName_844_, lean_object* v_expectedType_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_844_, v_expectedType_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(lean_object* v_00_u03b1_856_, lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_857_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(lean_object* v_00_u03b1_868_, lean_object* v_msg_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(v_00_u03b1_868_, v_msg_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object* v_opts_880_, lean_object* v_opt_881_){
_start:
{
lean_object* v_name_882_; lean_object* v_defValue_883_; lean_object* v_map_884_; lean_object* v___x_885_; 
v_name_882_ = lean_ctor_get(v_opt_881_, 0);
v_defValue_883_ = lean_ctor_get(v_opt_881_, 1);
v_map_884_ = lean_ctor_get(v_opts_880_, 0);
v___x_885_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_884_, v_name_882_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_inc(v_defValue_883_);
return v_defValue_883_;
}
else
{
lean_object* v_val_886_; 
v_val_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v___x_885_, 1);
if (lean_obj_tag(v_val_886_) == 3)
{
lean_object* v_v_887_; 
v_v_887_ = lean_ctor_get(v_val_886_, 0);
lean_inc(v_v_887_);
lean_dec_ref_known(v_val_886_, 1);
return v_v_887_;
}
else
{
lean_dec(v_val_886_);
lean_inc(v_defValue_883_);
return v_defValue_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object* v_opts_888_, lean_object* v_opt_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_opts_888_, v_opt_889_);
lean_dec_ref(v_opt_889_);
lean_dec_ref(v_opts_888_);
return v_res_890_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
if (lean_obj_tag(v_x_892_) == 0)
{
uint8_t v___x_893_; 
v___x_893_ = 1;
return v___x_893_;
}
else
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
}
else
{
if (lean_obj_tag(v_x_892_) == 0)
{
uint8_t v___x_895_; 
v___x_895_ = 0;
return v___x_895_;
}
else
{
lean_object* v_val_896_; lean_object* v_val_897_; uint8_t v___x_898_; 
v_val_896_ = lean_ctor_get(v_x_891_, 0);
v_val_897_ = lean_ctor_get(v_x_892_, 0);
v___x_898_ = lean_name_eq(v_val_896_, v_val_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_x_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_x_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Meta_saveState___redArg(v___y_905_, v___y_907_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_r_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
v_r_911_ = lean_apply_5(v_x_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
if (lean_obj_tag(v_r_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v_r_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v_r_911_, 1);
v___x_913_ = l_Lean_Meta_SavedState_restore___redArg(v_a_910_, v___y_905_, v___y_907_);
lean_dec(v_a_910_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_921_);
v___x_915_ = v___x_913_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___x_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v_a_912_);
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_912_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_912_);
v_a_922_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_913_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_913_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_931_; 
v_a_930_ = lean_ctor_get(v_r_911_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v_r_911_, 1);
v___x_931_ = l_Lean_Meta_SavedState_restore___redArg(v_a_910_, v___y_905_, v___y_907_);
lean_dec(v_a_910_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_931_, 0);
lean_dec(v_unused_939_);
v___x_933_ = v___x_931_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_dec(v___x_931_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
lean_ctor_set(v___x_933_, 0, v_a_930_);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_930_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_930_);
v_a_940_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_931_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_931_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_x_903_);
v_a_948_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_909_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_909_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg___boxed(lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(lean_object* v_00_u03b1_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v_x_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___boxed(lean_object* v_00_u03b1_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(v_00_u03b1_971_, v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object* v_cs_979_, lean_object* v_n_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_array_push(v_cs_979_, v_n_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object* v_cs_983_, lean_object* v_n_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(v_cs_983_, v_n_984_, v_x_985_);
lean_dec(v_x_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___lam__0(lean_object* v_f_987_, lean_object* v_x1_988_, lean_object* v_x2_989_, lean_object* v_x3_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = lean_apply_3(v_f_987_, v_x1_988_, v_x2_989_, v_x3_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(lean_object* v_f_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_i_995_, lean_object* v_acc_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_array_get_size(v_keys_993_);
v___x_998_ = lean_nat_dec_lt(v_i_995_, v___x_997_);
if (v___x_998_ == 0)
{
lean_dec(v_i_995_);
lean_dec(v_f_992_);
return v_acc_996_;
}
else
{
lean_object* v_k_999_; lean_object* v_v_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_k_999_ = lean_array_fget_borrowed(v_keys_993_, v_i_995_);
v_v_1000_ = lean_array_fget_borrowed(v_vals_994_, v_i_995_);
lean_inc(v_f_992_);
lean_inc(v_v_1000_);
lean_inc(v_k_999_);
v___x_1001_ = lean_apply_3(v_f_992_, v_acc_996_, v_k_999_, v_v_1000_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_i_995_, v___x_1002_);
lean_dec(v_i_995_);
v_i_995_ = v___x_1003_;
v_acc_996_ = v___x_1001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_f_1005_, lean_object* v_keys_1006_, lean_object* v_vals_1007_, lean_object* v_i_1008_, lean_object* v_acc_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(v_f_1005_, v_keys_1006_, v_vals_1007_, v_i_1008_, v_acc_1009_);
lean_dec_ref(v_vals_1007_);
lean_dec_ref(v_keys_1006_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(lean_object* v_f_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
lean_object* v_es_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_es_1014_ = lean_ctor_get(v_x_1012_, 0);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_array_get_size(v_es_1014_);
v___x_1017_ = lean_nat_dec_lt(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_f_1011_);
return v_x_1013_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_le(v___x_1016_, v___x_1016_);
if (v___x_1018_ == 0)
{
if (v___x_1017_ == 0)
{
lean_dec(v_f_1011_);
return v_x_1013_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1016_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_1011_, v_es_1014_, v___x_1019_, v___x_1020_, v_x_1013_);
return v___x_1021_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1016_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_1011_, v_es_1014_, v___x_1022_, v___x_1023_, v_x_1013_);
return v___x_1024_;
}
}
}
else
{
lean_object* v_ks_1025_; lean_object* v_vs_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_ks_1025_ = lean_ctor_get(v_x_1012_, 0);
v_vs_1026_ = lean_ctor_get(v_x_1012_, 1);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(v_f_1011_, v_ks_1025_, v_vs_1026_, v___x_1027_, v_x_1013_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(lean_object* v_f_1029_, lean_object* v_as_1030_, size_t v_i_1031_, size_t v_stop_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v___y_1035_; uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1031_, v_stop_1032_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1030_, v_i_1031_);
switch(lean_obj_tag(v___x_1040_))
{
case 0:
{
lean_object* v_key_1041_; lean_object* v_val_1042_; lean_object* v___x_1043_; 
v_key_1041_ = lean_ctor_get(v___x_1040_, 0);
v_val_1042_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_f_1029_);
lean_inc(v_val_1042_);
lean_inc(v_key_1041_);
v___x_1043_ = lean_apply_3(v_f_1029_, v_b_1033_, v_key_1041_, v_val_1042_);
v___y_1035_ = v___x_1043_;
goto v___jp_1034_;
}
case 1:
{
lean_object* v_node_1044_; lean_object* v___x_1045_; 
v_node_1044_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_f_1029_);
v___x_1045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_1029_, v_node_1044_, v_b_1033_);
v___y_1035_ = v___x_1045_;
goto v___jp_1034_;
}
default: 
{
v___y_1035_ = v_b_1033_;
goto v___jp_1034_;
}
}
}
else
{
lean_dec(v_f_1029_);
return v_b_1033_;
}
v___jp_1034_:
{
size_t v___x_1036_; size_t v___x_1037_; 
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1031_, v___x_1036_);
v_i_1031_ = v___x_1037_;
v_b_1033_ = v___y_1035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_f_1046_, lean_object* v_as_1047_, lean_object* v_i_1048_, lean_object* v_stop_1049_, lean_object* v_b_1050_){
_start:
{
size_t v_i_boxed_1051_; size_t v_stop_boxed_1052_; lean_object* v_res_1053_; 
v_i_boxed_1051_ = lean_unbox_usize(v_i_1048_);
lean_dec(v_i_1048_);
v_stop_boxed_1052_ = lean_unbox_usize(v_stop_1049_);
lean_dec(v_stop_1049_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_1046_, v_as_1047_, v_i_boxed_1051_, v_stop_boxed_1052_, v_b_1050_);
lean_dec_ref(v_as_1047_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_1054_, v_x_1055_, v_x_1056_);
lean_dec_ref(v_x_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(lean_object* v_map_1058_, lean_object* v_f_1059_, lean_object* v_init_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; 
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1061_, 0, v_f_1059_);
v___x_1062_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v___f_1061_, v_map_1058_, v_init_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___boxed(lean_object* v_map_1063_, lean_object* v_f_1064_, lean_object* v_init_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(v_map_1063_, v_f_1064_, v_init_1065_);
lean_dec_ref(v_map_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object* v_o_1070_, lean_object* v_k_1071_, uint8_t v_v_1072_){
_start:
{
lean_object* v_map_1073_; uint8_t v_hasTrace_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1088_; 
v_map_1073_ = lean_ctor_get(v_o_1070_, 0);
v_hasTrace_1074_ = lean_ctor_get_uint8(v_o_1070_, sizeof(void*)*1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_o_1070_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1076_ = v_o_1070_;
v_isShared_1077_ = v_isSharedCheck_1088_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_map_1073_);
lean_dec(v_o_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1088_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1078_, 0, v_v_1072_);
lean_inc(v_k_1071_);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1071_, v___x_1078_, v_map_1073_);
if (v_hasTrace_1074_ == 0)
{
lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1));
v___x_1081_ = l_Lean_Name_isPrefixOf(v___x_1080_, v_k_1071_);
lean_dec(v_k_1071_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1079_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1081_);
return v___x_1083_;
}
}
else
{
lean_object* v___x_1086_; 
lean_dec(v_k_1071_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1086_ = v___x_1076_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1087_, sizeof(void*)*1, v_hasTrace_1074_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object* v_o_1089_, lean_object* v_k_1090_, lean_object* v_v_1091_){
_start:
{
uint8_t v_v_boxed_1092_; lean_object* v_res_1093_; 
v_v_boxed_1092_ = lean_unbox(v_v_1091_);
v_res_1093_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_o_1089_, v_k_1090_, v_v_boxed_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object* v_opts_1094_, lean_object* v_opt_1095_, uint8_t v_val_1096_){
_start:
{
lean_object* v_name_1097_; lean_object* v___x_1098_; 
v_name_1097_ = lean_ctor_get(v_opt_1095_, 0);
lean_inc(v_name_1097_);
lean_dec_ref(v_opt_1095_);
v___x_1098_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_opts_1094_, v_name_1097_, v_val_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object* v_opts_1099_, lean_object* v_opt_1100_, lean_object* v_val_1101_){
_start:
{
uint8_t v_val_boxed_1102_; lean_object* v_res_1103_; 
v_val_boxed_1102_ = lean_unbox(v_val_1101_);
v_res_1103_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_opts_1099_, v_opt_1100_, v_val_boxed_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
if (lean_obj_tag(v_a_1104_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = l_List_reverse___redArg(v_a_1105_);
return v___x_1106_;
}
else
{
lean_object* v_head_1107_; lean_object* v_tail_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1117_; 
v_head_1107_ = lean_ctor_get(v_a_1104_, 0);
v_tail_1108_ = lean_ctor_get(v_a_1104_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_1104_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1110_ = v_a_1104_;
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_tail_1108_);
lean_inc(v_head_1107_);
lean_dec(v_a_1104_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = l_Lean_mkLevelParam(v_head_1107_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_a_1105_);
lean_ctor_set(v___x_1110_, 0, v___x_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_a_1105_);
v___x_1114_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
v_a_1104_ = v_tail_1108_;
v_a_1105_ = v___x_1114_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__0);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
lean_ctor_set(v___x_1123_, 3, v___x_1122_);
lean_ctor_set(v___x_1123_, 4, v___x_1121_);
lean_ctor_set(v___x_1123_, 5, v___x_1121_);
lean_ctor_set(v___x_1123_, 6, v___x_1121_);
lean_ctor_set(v___x_1123_, 7, v___x_1121_);
lean_ctor_set(v___x_1123_, 8, v___x_1121_);
lean_ctor_set(v___x_1123_, 9, v___x_1121_);
lean_ctor_set(v___x_1123_, 10, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_unsigned_to_nat(32u);
v___x_1125_ = lean_mk_empty_array_with_capacity(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1127_ = ((size_t)5ULL);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_unsigned_to_nat(32u);
v___x_1130_ = lean_mk_empty_array_with_capacity(v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__3);
v___x_1132_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1130_);
lean_ctor_set(v___x_1132_, 2, v___x_1128_);
lean_ctor_set(v___x_1132_, 3, v___x_1128_);
lean_ctor_set_usize(v___x_1132_, 4, v___x_1127_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = lean_box(1);
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__4);
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__1);
v___x_1136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
lean_ctor_set(v___x_1136_, 2, v___x_1133_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__6));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__8));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__10));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__12));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__14));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__16));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__18));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg(lean_object* v_msg_1158_, lean_object* v_declHint_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v_env_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_st_ref_get(v___y_1160_);
v_env_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_ref(v_env_1163_);
lean_dec(v___x_1162_);
v___x_1164_ = l_Lean_Name_isAnonymous(v_declHint_1159_);
if (v___x_1164_ == 0)
{
uint8_t v_isExporting_1165_; 
v_isExporting_1165_ = lean_ctor_get_uint8(v_env_1163_, sizeof(void*)*8);
if (v_isExporting_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_env_1163_);
lean_dec(v_declHint_1159_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_msg_1158_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
lean_inc_ref(v_env_1163_);
v___x_1167_ = l_Lean_Environment_setExporting(v_env_1163_, v___x_1164_);
lean_inc(v_declHint_1159_);
lean_inc_ref(v___x_1167_);
v___x_1168_ = l_Lean_Environment_contains(v___x_1167_, v_declHint_1159_, v_isExporting_1165_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v___x_1167_);
lean_dec_ref(v_env_1163_);
lean_dec(v_declHint_1159_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_msg_1158_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_c_1175_; lean_object* v___x_1176_; 
v___x_1170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__2);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__5);
v___x_1172_ = l_Lean_Options_empty;
v___x_1173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1167_);
lean_ctor_set(v___x_1173_, 1, v___x_1170_);
lean_ctor_set(v___x_1173_, 2, v___x_1171_);
lean_ctor_set(v___x_1173_, 3, v___x_1172_);
lean_inc(v_declHint_1159_);
v___x_1174_ = l_Lean_MessageData_ofConstName(v_declHint_1159_, v___x_1164_);
v_c_1175_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1175_, 0, v___x_1173_);
lean_ctor_set(v_c_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1163_, v_declHint_1159_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref(v_env_1163_);
lean_dec(v_declHint_1159_);
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_c_1175_);
v___x_1179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__9);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_MessageData_note(v___x_1180_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_msg_1158_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v_val_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1219_; 
v_val_1184_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1186_ = v___x_1176_;
v_isShared_1187_ = v_isSharedCheck_1219_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_val_1184_);
lean_dec(v___x_1176_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1219_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_mod_1191_; uint8_t v___x_1192_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = l_Lean_Environment_header(v_env_1163_);
lean_dec_ref(v_env_1163_);
v___x_1190_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1189_);
v_mod_1191_ = lean_array_get(v___x_1188_, v___x_1190_, v_val_1184_);
lean_dec(v_val_1184_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = l_Lean_isPrivateName(v_declHint_1159_);
lean_dec(v_declHint_1159_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__11);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_c_1175_);
v___x_1195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__13);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_MessageData_ofName(v_mod_1191_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Lean_MessageData_note(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_msg_1158_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1202_);
v___x_1204_ = v___x_1186_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__7);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v_c_1175_);
v___x_1208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__17);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_MessageData_ofName(v_mod_1191_);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__19);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_MessageData_note(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_msg_1158_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1215_);
v___x_1217_ = v___x_1186_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1220_; 
lean_dec_ref(v_env_1163_);
lean_dec(v_declHint_1159_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_msg_1158_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___boxed(lean_object* v_msg_1221_, lean_object* v_declHint_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_1221_, v_declHint_1222_, v___y_1223_);
lean_dec(v___y_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17(lean_object* v_msg_1226_, lean_object* v_declHint_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1243_; 
v___x_1233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_1226_, v_declHint_1227_, v___y_1231_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1243_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1243_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = l_Lean_unknownIdentifierMessageTag;
v___x_1239_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v_a_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1239_);
v___x_1241_ = v___x_1236_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* v_msg_1244_, lean_object* v_declHint_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17(v_msg_1244_, v_declHint_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg(lean_object* v_msg_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_ref_1258_; lean_object* v___x_1259_; lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
v_ref_1258_ = lean_ctor_get(v___y_1255_, 5);
v___x_1259_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
lean_inc(v_ref_1258_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_ref_1258_);
lean_ctor_set(v___x_1264_, 1, v_a_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 1);
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg___boxed(lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(lean_object* v_ref_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_fileName_1283_; lean_object* v_fileMap_1284_; lean_object* v_options_1285_; lean_object* v_currRecDepth_1286_; lean_object* v_maxRecDepth_1287_; lean_object* v_ref_1288_; lean_object* v_currNamespace_1289_; lean_object* v_openDecls_1290_; lean_object* v_initHeartbeats_1291_; lean_object* v_maxHeartbeats_1292_; lean_object* v_quotContext_1293_; lean_object* v_currMacroScope_1294_; uint8_t v_diag_1295_; lean_object* v_cancelTk_x3f_1296_; uint8_t v_suppressElabErrors_1297_; lean_object* v_inheritedTraceOptions_1298_; lean_object* v_ref_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_fileName_1283_ = lean_ctor_get(v___y_1280_, 0);
v_fileMap_1284_ = lean_ctor_get(v___y_1280_, 1);
v_options_1285_ = lean_ctor_get(v___y_1280_, 2);
v_currRecDepth_1286_ = lean_ctor_get(v___y_1280_, 3);
v_maxRecDepth_1287_ = lean_ctor_get(v___y_1280_, 4);
v_ref_1288_ = lean_ctor_get(v___y_1280_, 5);
v_currNamespace_1289_ = lean_ctor_get(v___y_1280_, 6);
v_openDecls_1290_ = lean_ctor_get(v___y_1280_, 7);
v_initHeartbeats_1291_ = lean_ctor_get(v___y_1280_, 8);
v_maxHeartbeats_1292_ = lean_ctor_get(v___y_1280_, 9);
v_quotContext_1293_ = lean_ctor_get(v___y_1280_, 10);
v_currMacroScope_1294_ = lean_ctor_get(v___y_1280_, 11);
v_diag_1295_ = lean_ctor_get_uint8(v___y_1280_, sizeof(void*)*14);
v_cancelTk_x3f_1296_ = lean_ctor_get(v___y_1280_, 12);
v_suppressElabErrors_1297_ = lean_ctor_get_uint8(v___y_1280_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1298_ = lean_ctor_get(v___y_1280_, 13);
v_ref_1299_ = l_Lean_replaceRef(v_ref_1276_, v_ref_1288_);
lean_inc_ref(v_inheritedTraceOptions_1298_);
lean_inc(v_cancelTk_x3f_1296_);
lean_inc(v_currMacroScope_1294_);
lean_inc(v_quotContext_1293_);
lean_inc(v_maxHeartbeats_1292_);
lean_inc(v_initHeartbeats_1291_);
lean_inc(v_openDecls_1290_);
lean_inc(v_currNamespace_1289_);
lean_inc(v_maxRecDepth_1287_);
lean_inc(v_currRecDepth_1286_);
lean_inc_ref(v_options_1285_);
lean_inc_ref(v_fileMap_1284_);
lean_inc_ref(v_fileName_1283_);
v___x_1300_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1300_, 0, v_fileName_1283_);
lean_ctor_set(v___x_1300_, 1, v_fileMap_1284_);
lean_ctor_set(v___x_1300_, 2, v_options_1285_);
lean_ctor_set(v___x_1300_, 3, v_currRecDepth_1286_);
lean_ctor_set(v___x_1300_, 4, v_maxRecDepth_1287_);
lean_ctor_set(v___x_1300_, 5, v_ref_1299_);
lean_ctor_set(v___x_1300_, 6, v_currNamespace_1289_);
lean_ctor_set(v___x_1300_, 7, v_openDecls_1290_);
lean_ctor_set(v___x_1300_, 8, v_initHeartbeats_1291_);
lean_ctor_set(v___x_1300_, 9, v_maxHeartbeats_1292_);
lean_ctor_set(v___x_1300_, 10, v_quotContext_1293_);
lean_ctor_set(v___x_1300_, 11, v_currMacroScope_1294_);
lean_ctor_set(v___x_1300_, 12, v_cancelTk_x3f_1296_);
lean_ctor_set(v___x_1300_, 13, v_inheritedTraceOptions_1298_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*14, v_diag_1295_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*14 + 1, v_suppressElabErrors_1297_);
v___x_1301_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_1277_, v___y_1278_, v___y_1279_, v___x_1300_, v___y_1281_);
lean_dec_ref_known(v___x_1300_, 14);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg___boxed(lean_object* v_ref_1302_, lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(v_ref_1302_, v_msg_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v_ref_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg(lean_object* v_ref_1310_, lean_object* v_msg_1311_, lean_object* v_declHint_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v_a_1319_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17(v_msg_1311_, v_declHint_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(v_ref_1310_, v_a_1319_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_ref_1321_, lean_object* v_msg_1322_, lean_object* v_declHint_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg(v_ref_1321_, v_msg_1322_, v_declHint_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v_ref_1321_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__0));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__2));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg(lean_object* v_ref_1336_, lean_object* v_constName_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1343_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__1);
v___x_1344_ = 0;
lean_inc(v_constName_1337_);
v___x_1345_ = l_Lean_MessageData_ofConstName(v_constName_1337_, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg(v_ref_1336_, v___x_1348_, v_constName_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_ref_1350_, lean_object* v_constName_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg(v_ref_1350_, v_constName_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v_ref_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg(lean_object* v_constName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_ref_1364_; lean_object* v___x_1365_; 
v_ref_1364_ = lean_ctor_get(v___y_1361_, 5);
v___x_1365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg(v_ref_1364_, v_constName_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_constName_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg(v_constName_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_env_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1379_ = lean_st_ref_get(v___y_1377_);
v_env_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_env_1380_);
lean_dec(v___x_1379_);
v___x_1381_ = 0;
lean_inc(v_constName_1373_);
v___x_1382_ = l_Lean_Environment_findConstVal_x3f(v_env_1380_, v_constName_1373_, v___x_1381_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg(v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_constName_1373_);
v_val_1384_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 0);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_val_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3___boxed(lean_object* v_constName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
lean_inc(v_constName_1399_);
v___x_1405_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1417_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1417_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1417_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_levelParams_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v_levelParams_1410_ = lean_ctor_get(v_a_1406_, 1);
lean_inc(v_levelParams_1410_);
lean_dec(v_a_1406_);
v___x_1411_ = lean_box(0);
v___x_1412_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(v_levelParams_1410_, v___x_1411_);
v___x_1413_ = l_Lean_mkConst(v_constName_1399_, v___x_1412_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1413_);
v___x_1415_ = v___x_1408_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_constName_1399_);
v_a_1418_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1405_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1405_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object* v_constName_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_constName_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(lean_object* v_as_1435_, size_t v_i_1436_, size_t v_stop_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_eq(v_i_1436_, v_stop_1437_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_array_uget_borrowed(v_as_1435_, v_i_1436_);
lean_inc(v___x_1445_);
v___x_1446_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v___x_1445_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_n(v_a_1447_, 2);
lean_dec_ref_known(v___x_1446_, 1);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
v___x_1448_ = lean_infer_type(v_a_1447_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = l_Lean_Meta_isClass_x3f(v_a_1449_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v_a_1453_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___closed__0));
v___x_1458_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_a_1451_, v___x_1457_);
lean_dec(v_a_1451_);
if (v___x_1458_ == 0)
{
lean_dec(v_a_1447_);
v_a_1453_ = v_b_1438_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1459_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3);
v___x_1460_ = l_Lean_MessageData_ofConst(v_a_1447_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___x_1459_);
v___x_1463_ = lean_array_push(v_b_1438_, v___x_1462_);
v_a_1453_ = v___x_1463_;
goto v___jp_1452_;
}
v___jp_1452_:
{
size_t v___x_1454_; size_t v___x_1455_; 
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1436_, v___x_1454_);
v_i_1436_ = v___x_1455_;
v_b_1438_ = v_a_1453_;
goto _start;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1447_);
lean_dec_ref(v_b_1438_);
v_a_1464_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1450_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1450_);
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
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1447_);
lean_dec_ref(v_b_1438_);
v_a_1472_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1448_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1448_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_b_1438_);
v_a_1480_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1446_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1446_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_b_1438_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___boxed(lean_object* v_as_1489_, lean_object* v_i_1490_, lean_object* v_stop_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
size_t v_i_boxed_1498_; size_t v_stop_boxed_1499_; lean_object* v_res_1500_; 
v_i_boxed_1498_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_stop_boxed_1499_ = lean_unbox_usize(v_stop_1491_);
lean_dec(v_stop_1491_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_as_1489_, v_i_boxed_1498_, v_stop_boxed_1499_, v_b_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec_ref(v_as_1489_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object* v_as_1503_, lean_object* v_start_1504_, lean_object* v_stop_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___closed__0));
v___x_1512_ = lean_nat_dec_lt(v_start_1504_, v_stop_1505_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_array_get_size(v_as_1503_);
v___x_1515_ = lean_nat_dec_le(v_stop_1505_, v___x_1514_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_nat_dec_lt(v_start_1504_, v___x_1514_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1511_);
return v___x_1517_;
}
else
{
size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_usize_of_nat(v_start_1504_);
v___x_1519_ = lean_usize_of_nat(v___x_1514_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_as_1503_, v___x_1518_, v___x_1519_, v___x_1511_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1520_;
}
}
else
{
size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_usize_of_nat(v_start_1504_);
v___x_1522_ = lean_usize_of_nat(v_stop_1505_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_as_1503_, v___x_1521_, v___x_1522_, v___x_1511_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object* v_as_1524_, lean_object* v_start_1525_, lean_object* v_stop_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v_as_1524_, v_start_1525_, v_stop_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v_stop_1526_);
lean_dec(v_start_1525_);
lean_dec_ref(v_as_1524_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(lean_object* v_hi_1533_, lean_object* v_pivot_1534_, lean_object* v_as_1535_, lean_object* v_i_1536_, lean_object* v_k_1537_){
_start:
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_nat_dec_lt(v_k_1537_, v_hi_1533_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v_k_1537_);
v___x_1539_ = lean_array_fswap(v_as_1535_, v_i_1536_, v_hi_1533_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_i_1536_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = lean_array_fget_borrowed(v_as_1535_, v_k_1537_);
v___x_1542_ = l_Lean_Name_lt(v___x_1541_, v_pivot_1534_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_add(v_k_1537_, v___x_1543_);
lean_dec(v_k_1537_);
v_k_1537_ = v___x_1544_;
goto _start;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = lean_array_fswap(v_as_1535_, v_i_1536_, v_k_1537_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_i_1536_, v___x_1547_);
lean_dec(v_i_1536_);
v___x_1549_ = lean_nat_add(v_k_1537_, v___x_1547_);
lean_dec(v_k_1537_);
v_as_1535_ = v___x_1546_;
v_i_1536_ = v___x_1548_;
v_k_1537_ = v___x_1549_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg___boxed(lean_object* v_hi_1551_, lean_object* v_pivot_1552_, lean_object* v_as_1553_, lean_object* v_i_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(v_hi_1551_, v_pivot_1552_, v_as_1553_, v_i_1554_, v_k_1555_);
lean_dec(v_pivot_1552_);
lean_dec(v_hi_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(lean_object* v_n_1557_, lean_object* v_as_1558_, lean_object* v_lo_1559_, lean_object* v_hi_1560_){
_start:
{
lean_object* v___y_1562_; uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_lt(v_lo_1559_, v_hi_1560_);
if (v___x_1572_ == 0)
{
lean_dec(v_lo_1559_);
return v_as_1558_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_mid_1575_; lean_object* v___y_1577_; lean_object* v___y_1583_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1573_ = lean_nat_add(v_lo_1559_, v_hi_1560_);
v___x_1574_ = lean_unsigned_to_nat(1u);
v_mid_1575_ = lean_nat_shiftr(v___x_1573_, v___x_1574_);
lean_dec(v___x_1573_);
v___x_1588_ = lean_array_fget_borrowed(v_as_1558_, v_mid_1575_);
v___x_1589_ = lean_array_fget_borrowed(v_as_1558_, v_lo_1559_);
v___x_1590_ = l_Lean_Name_lt(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
v___y_1583_ = v_as_1558_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_array_fswap(v_as_1558_, v_lo_1559_, v_mid_1575_);
v___y_1583_ = v___x_1591_;
goto v___jp_1582_;
}
v___jp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = lean_array_fget_borrowed(v___y_1577_, v_mid_1575_);
v___x_1579_ = lean_array_fget_borrowed(v___y_1577_, v_hi_1560_);
v___x_1580_ = l_Lean_Name_lt(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec(v_mid_1575_);
v___y_1562_ = v___y_1577_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_array_fswap(v___y_1577_, v_mid_1575_, v_hi_1560_);
lean_dec(v_mid_1575_);
v___y_1562_ = v___x_1581_;
goto v___jp_1561_;
}
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = lean_array_fget_borrowed(v___y_1583_, v_hi_1560_);
v___x_1585_ = lean_array_fget_borrowed(v___y_1583_, v_lo_1559_);
v___x_1586_ = l_Lean_Name_lt(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
v___y_1577_ = v___y_1583_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_array_fswap(v___y_1583_, v_lo_1559_, v_hi_1560_);
v___y_1577_ = v___x_1587_;
goto v___jp_1576_;
}
}
}
v___jp_1561_:
{
lean_object* v_pivot_1563_; lean_object* v___x_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; uint8_t v___x_1567_; 
v_pivot_1563_ = lean_array_fget(v___y_1562_, v_hi_1560_);
lean_inc_n(v_lo_1559_, 2);
v___x_1564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(v_hi_1560_, v_pivot_1563_, v___y_1562_, v_lo_1559_, v_lo_1559_);
lean_dec(v_pivot_1563_);
v_fst_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec_ref(v___x_1564_);
v___x_1567_ = lean_nat_dec_le(v_hi_1560_, v_fst_1565_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_n_1557_, v_snd_1566_, v_lo_1559_, v_fst_1565_);
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_add(v_fst_1565_, v___x_1569_);
lean_dec(v_fst_1565_);
v_as_1558_ = v___x_1568_;
v_lo_1559_ = v___x_1570_;
goto _start;
}
else
{
lean_dec(v_fst_1565_);
lean_dec(v_lo_1559_);
return v_snd_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(lean_object* v_n_1592_, lean_object* v_as_1593_, lean_object* v_lo_1594_, lean_object* v_hi_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_n_1592_, v_as_1593_, v_lo_1594_, v_hi_1595_);
lean_dec(v_hi_1595_);
lean_dec(v_n_1592_);
return v_res_1596_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1599_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2);
v___x_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
lean_ctor_set(v___x_1603_, 2, v___x_1602_);
lean_ctor_set(v___x_1603_, 3, v___x_1602_);
lean_ctor_set(v___x_1603_, 4, v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1604_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object* v_s_1609_, lean_object* v___f_1610_, uint8_t v___x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___x_1707_; lean_object* v_fileName_1708_; lean_object* v_fileMap_1709_; lean_object* v_options_1710_; lean_object* v_currRecDepth_1711_; lean_object* v_ref_1712_; lean_object* v_currNamespace_1713_; lean_object* v_openDecls_1714_; lean_object* v_initHeartbeats_1715_; lean_object* v_maxHeartbeats_1716_; lean_object* v_quotContext_1717_; lean_object* v_currMacroScope_1718_; lean_object* v_cancelTk_x3f_1719_; uint8_t v_suppressElabErrors_1720_; lean_object* v_inheritedTraceOptions_1721_; lean_object* v_env_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v_fileName_1727_; lean_object* v_fileMap_1728_; lean_object* v_currRecDepth_1729_; lean_object* v_ref_1730_; lean_object* v_currNamespace_1731_; lean_object* v_openDecls_1732_; lean_object* v_initHeartbeats_1733_; lean_object* v_maxHeartbeats_1734_; lean_object* v_quotContext_1735_; lean_object* v_currMacroScope_1736_; lean_object* v_cancelTk_x3f_1737_; uint8_t v_suppressElabErrors_1738_; lean_object* v_inheritedTraceOptions_1739_; lean_object* v___y_1740_; uint8_t v___y_1771_; uint8_t v___x_1792_; 
v___x_1707_ = lean_st_ref_get(v___y_1615_);
v_fileName_1708_ = lean_ctor_get(v___y_1614_, 0);
v_fileMap_1709_ = lean_ctor_get(v___y_1614_, 1);
v_options_1710_ = lean_ctor_get(v___y_1614_, 2);
v_currRecDepth_1711_ = lean_ctor_get(v___y_1614_, 3);
v_ref_1712_ = lean_ctor_get(v___y_1614_, 5);
v_currNamespace_1713_ = lean_ctor_get(v___y_1614_, 6);
v_openDecls_1714_ = lean_ctor_get(v___y_1614_, 7);
v_initHeartbeats_1715_ = lean_ctor_get(v___y_1614_, 8);
v_maxHeartbeats_1716_ = lean_ctor_get(v___y_1614_, 9);
v_quotContext_1717_ = lean_ctor_get(v___y_1614_, 10);
v_currMacroScope_1718_ = lean_ctor_get(v___y_1614_, 11);
v_cancelTk_x3f_1719_ = lean_ctor_get(v___y_1614_, 12);
v_suppressElabErrors_1720_ = lean_ctor_get_uint8(v___y_1614_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1721_ = lean_ctor_get(v___y_1614_, 13);
v_env_1722_ = lean_ctor_get(v___x_1707_, 0);
lean_inc_ref(v_env_1722_);
lean_dec(v___x_1707_);
v___x_1723_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1710_);
v___x_1724_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_1710_, v___x_1723_, v___x_1611_);
v___x_1725_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_1724_, v___x_1723_);
v___x_1792_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1722_);
lean_dec_ref(v_env_1722_);
if (v___x_1792_ == 0)
{
if (v___x_1725_ == 0)
{
v_fileName_1727_ = v_fileName_1708_;
v_fileMap_1728_ = v_fileMap_1709_;
v_currRecDepth_1729_ = v_currRecDepth_1711_;
v_ref_1730_ = v_ref_1712_;
v_currNamespace_1731_ = v_currNamespace_1713_;
v_openDecls_1732_ = v_openDecls_1714_;
v_initHeartbeats_1733_ = v_initHeartbeats_1715_;
v_maxHeartbeats_1734_ = v_maxHeartbeats_1716_;
v_quotContext_1735_ = v_quotContext_1717_;
v_currMacroScope_1736_ = v_currMacroScope_1718_;
v_cancelTk_x3f_1737_ = v_cancelTk_x3f_1719_;
v_suppressElabErrors_1738_ = v_suppressElabErrors_1720_;
v_inheritedTraceOptions_1739_ = v_inheritedTraceOptions_1721_;
v___y_1740_ = v___y_1615_;
goto v___jp_1726_;
}
else
{
v___y_1771_ = v___x_1792_;
goto v___jp_1770_;
}
}
else
{
v___y_1771_ = v___x_1725_;
goto v___jp_1770_;
}
v___jp_1617_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_array_get_size(v___y_1622_);
v___x_1624_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v___y_1622_, v___y_1618_, v___x_1623_, v___y_1612_, v___y_1613_, v___y_1621_, v___y_1620_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1619_);
lean_ctor_set(v___x_1629_, 1, v_a_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec_ref(v___y_1619_);
v_a_1634_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1624_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1624_);
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
v___jp_1642_:
{
lean_object* v___x_1651_; 
v___x_1651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v___y_1643_, v___y_1647_, v___y_1648_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec(v___y_1643_);
v___y_1618_ = v___y_1644_;
v___y_1619_ = v___y_1646_;
v___y_1620_ = v___y_1645_;
v___y_1621_ = v___y_1649_;
v___y_1622_ = v___x_1651_;
goto v___jp_1617_;
}
v___jp_1652_:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_le(v___y_1660_, v___y_1655_);
if (v___x_1661_ == 0)
{
lean_dec(v___y_1655_);
lean_inc(v___y_1660_);
v___y_1643_ = v___y_1653_;
v___y_1644_ = v___y_1654_;
v___y_1645_ = v___y_1658_;
v___y_1646_ = v___y_1657_;
v___y_1647_ = v___y_1656_;
v___y_1648_ = v___y_1660_;
v___y_1649_ = v___y_1659_;
v___y_1650_ = v___y_1660_;
goto v___jp_1642_;
}
else
{
v___y_1643_ = v___y_1653_;
v___y_1644_ = v___y_1654_;
v___y_1645_ = v___y_1658_;
v___y_1646_ = v___y_1657_;
v___y_1647_ = v___y_1656_;
v___y_1648_ = v___y_1660_;
v___y_1649_ = v___y_1659_;
v___y_1650_ = v___y_1655_;
goto v___jp_1642_;
}
}
v___jp_1662_:
{
lean_object* v_keyedConfig_1666_; uint8_t v_trackZetaDelta_1667_; lean_object* v_zetaDeltaSet_1668_; lean_object* v_lctx_1669_; lean_object* v_localInstances_1670_; lean_object* v_defEqCtx_x3f_1671_; lean_object* v_synthPendingDepth_1672_; lean_object* v_customCanUnfoldPredicate_x3f_1673_; uint8_t v_univApprox_1674_; uint8_t v_inTypeClassResolution_1675_; uint8_t v_cacheInferType_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_keyedConfig_1666_ = lean_ctor_get(v___y_1612_, 0);
v_trackZetaDelta_1667_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*7);
v_zetaDeltaSet_1668_ = lean_ctor_get(v___y_1612_, 1);
v_lctx_1669_ = lean_ctor_get(v___y_1612_, 2);
v_localInstances_1670_ = lean_ctor_get(v___y_1612_, 3);
v_defEqCtx_x3f_1671_ = lean_ctor_get(v___y_1612_, 4);
v_synthPendingDepth_1672_ = lean_ctor_get(v___y_1612_, 5);
v_customCanUnfoldPredicate_x3f_1673_ = lean_ctor_get(v___y_1612_, 6);
v_univApprox_1674_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1675_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*7 + 2);
v_cacheInferType_1676_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1666_);
v___x_1677_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_1665_, v_keyedConfig_1666_);
lean_inc(v_customCanUnfoldPredicate_x3f_1673_);
lean_inc(v_synthPendingDepth_1672_);
lean_inc(v_defEqCtx_x3f_1671_);
lean_inc_ref(v_localInstances_1670_);
lean_inc_ref(v_lctx_1669_);
lean_inc(v_zetaDeltaSet_1668_);
v___x_1678_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_zetaDeltaSet_1668_);
lean_ctor_set(v___x_1678_, 2, v_lctx_1669_);
lean_ctor_set(v___x_1678_, 3, v_localInstances_1670_);
lean_ctor_set(v___x_1678_, 4, v_defEqCtx_x3f_1671_);
lean_ctor_set(v___x_1678_, 5, v_synthPendingDepth_1672_);
lean_ctor_set(v___x_1678_, 6, v_customCanUnfoldPredicate_x3f_1673_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*7, v_trackZetaDelta_1667_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*7 + 1, v_univApprox_1674_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1675_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*7 + 3, v_cacheInferType_1676_);
lean_inc_ref(v___y_1664_);
v___x_1679_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1609_, v___x_1678_, v___y_1613_, v___y_1664_, v___y_1663_);
lean_dec_ref_known(v___x_1678_, 7);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v_diag_1682_; lean_object* v_unfoldCounter_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = lean_st_ref_get(v___y_1613_);
v_diag_1682_ = lean_ctor_get(v___x_1681_, 4);
lean_inc_ref(v_diag_1682_);
lean_dec(v___x_1681_);
v_unfoldCounter_1683_ = lean_ctor_get(v_diag_1682_, 0);
lean_inc_ref(v_unfoldCounter_1683_);
lean_dec_ref(v_diag_1682_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_1686_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(v_unfoldCounter_1683_, v___f_1610_, v___x_1685_);
lean_dec_ref(v_unfoldCounter_1683_);
v___x_1687_ = lean_array_get_size(v___x_1686_);
v___x_1688_ = lean_nat_dec_eq(v___x_1687_, v___x_1684_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_sub(v___x_1687_, v___x_1689_);
v___x_1691_ = lean_nat_dec_le(v___x_1684_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_inc(v___x_1690_);
v___y_1653_ = v___x_1687_;
v___y_1654_ = v___x_1684_;
v___y_1655_ = v___x_1690_;
v___y_1656_ = v___x_1686_;
v___y_1657_ = v_a_1680_;
v___y_1658_ = v___y_1663_;
v___y_1659_ = v___y_1664_;
v___y_1660_ = v___x_1690_;
goto v___jp_1652_;
}
else
{
v___y_1653_ = v___x_1687_;
v___y_1654_ = v___x_1684_;
v___y_1655_ = v___x_1690_;
v___y_1656_ = v___x_1686_;
v___y_1657_ = v_a_1680_;
v___y_1658_ = v___y_1663_;
v___y_1659_ = v___y_1664_;
v___y_1660_ = v___x_1684_;
goto v___jp_1652_;
}
}
else
{
v___y_1618_ = v___x_1684_;
v___y_1619_ = v_a_1680_;
v___y_1620_ = v___y_1663_;
v___y_1621_ = v___y_1664_;
v___y_1622_ = v___x_1686_;
goto v___jp_1617_;
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v___f_1610_);
v_a_1692_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1679_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1679_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
v___jp_1700_:
{
lean_object* v___x_1703_; uint8_t v_transparency_1704_; uint8_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1703_ = l_Lean_Meta_Context_config(v___y_1612_);
v_transparency_1704_ = lean_ctor_get_uint8(v___x_1703_, 9);
lean_dec_ref(v___x_1703_);
v___x_1705_ = 1;
v___x_1706_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
v___y_1663_ = v___y_1701_;
v___y_1664_ = v___y_1702_;
v___y_1665_ = v_transparency_1704_;
goto v___jp_1662_;
}
else
{
v___y_1663_ = v___y_1701_;
v___y_1664_ = v___y_1702_;
v___y_1665_ = v___x_1705_;
goto v___jp_1662_;
}
}
v___jp_1726_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = l_Lean_maxRecDepth;
v___x_1742_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_1724_, v___x_1741_);
lean_inc_ref(v_inheritedTraceOptions_1739_);
lean_inc(v_cancelTk_x3f_1737_);
lean_inc(v_currMacroScope_1736_);
lean_inc(v_quotContext_1735_);
lean_inc(v_maxHeartbeats_1734_);
lean_inc(v_initHeartbeats_1733_);
lean_inc(v_openDecls_1732_);
lean_inc(v_currNamespace_1731_);
lean_inc(v_ref_1730_);
lean_inc(v_currRecDepth_1729_);
lean_inc_ref(v_fileMap_1728_);
lean_inc_ref(v_fileName_1727_);
v___x_1743_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1743_, 0, v_fileName_1727_);
lean_ctor_set(v___x_1743_, 1, v_fileMap_1728_);
lean_ctor_set(v___x_1743_, 2, v___x_1724_);
lean_ctor_set(v___x_1743_, 3, v_currRecDepth_1729_);
lean_ctor_set(v___x_1743_, 4, v___x_1742_);
lean_ctor_set(v___x_1743_, 5, v_ref_1730_);
lean_ctor_set(v___x_1743_, 6, v_currNamespace_1731_);
lean_ctor_set(v___x_1743_, 7, v_openDecls_1732_);
lean_ctor_set(v___x_1743_, 8, v_initHeartbeats_1733_);
lean_ctor_set(v___x_1743_, 9, v_maxHeartbeats_1734_);
lean_ctor_set(v___x_1743_, 10, v_quotContext_1735_);
lean_ctor_set(v___x_1743_, 11, v_currMacroScope_1736_);
lean_ctor_set(v___x_1743_, 12, v_cancelTk_x3f_1737_);
lean_ctor_set(v___x_1743_, 13, v_inheritedTraceOptions_1739_);
lean_ctor_set_uint8(v___x_1743_, sizeof(void*)*14, v___x_1725_);
lean_ctor_set_uint8(v___x_1743_, sizeof(void*)*14 + 1, v_suppressElabErrors_1738_);
v___x_1744_ = l_Lean_isDiagnosticsEnabled___redArg(v___x_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; uint8_t v___x_1746_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = lean_unbox(v_a_1745_);
lean_dec(v_a_1745_);
if (v___x_1746_ == 0)
{
v___y_1701_ = v___y_1740_;
v___y_1702_ = v___x_1743_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1747_; lean_object* v_mctx_1748_; lean_object* v_cache_1749_; lean_object* v_zetaDeltaFVarIds_1750_; lean_object* v_postponed_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1760_; 
v___x_1747_ = lean_st_ref_take(v___y_1613_);
v_mctx_1748_ = lean_ctor_get(v___x_1747_, 0);
v_cache_1749_ = lean_ctor_get(v___x_1747_, 1);
v_zetaDeltaFVarIds_1750_ = lean_ctor_get(v___x_1747_, 2);
v_postponed_1751_ = lean_ctor_get(v___x_1747_, 3);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1747_, 4);
lean_dec(v_unused_1761_);
v___x_1753_ = v___x_1747_;
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_postponed_1751_);
lean_inc(v_zetaDeltaFVarIds_1750_);
lean_inc(v_cache_1749_);
lean_inc(v_mctx_1748_);
lean_dec(v___x_1747_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 4, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_mctx_1748_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_cache_1749_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_zetaDeltaFVarIds_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_postponed_1751_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_st_ref_put(v___y_1613_, v___x_1757_);
v___y_1701_ = v___y_1740_;
v___y_1702_ = v___x_1743_;
goto v___jp_1700_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref_known(v___x_1743_, 14);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v___f_1610_);
lean_dec_ref(v_s_1609_);
v_a_1762_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1744_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1744_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
v___jp_1770_:
{
if (v___y_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v_env_1773_; lean_object* v_nextMacroScope_1774_; lean_object* v_ngen_1775_; lean_object* v_auxDeclNGen_1776_; lean_object* v_traceState_1777_; lean_object* v_messages_1778_; lean_object* v_infoState_1779_; lean_object* v_snapshotTasks_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1790_; 
v___x_1772_ = lean_st_ref_take(v___y_1615_);
v_env_1773_ = lean_ctor_get(v___x_1772_, 0);
v_nextMacroScope_1774_ = lean_ctor_get(v___x_1772_, 1);
v_ngen_1775_ = lean_ctor_get(v___x_1772_, 2);
v_auxDeclNGen_1776_ = lean_ctor_get(v___x_1772_, 3);
v_traceState_1777_ = lean_ctor_get(v___x_1772_, 4);
v_messages_1778_ = lean_ctor_get(v___x_1772_, 6);
v_infoState_1779_ = lean_ctor_get(v___x_1772_, 7);
v_snapshotTasks_1780_ = lean_ctor_get(v___x_1772_, 8);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v___x_1772_, 5);
lean_dec(v_unused_1791_);
v___x_1782_ = v___x_1772_;
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snapshotTasks_1780_);
lean_inc(v_infoState_1779_);
lean_inc(v_messages_1778_);
lean_inc(v_traceState_1777_);
lean_inc(v_auxDeclNGen_1776_);
lean_inc(v_ngen_1775_);
lean_inc(v_nextMacroScope_1774_);
lean_inc(v_env_1773_);
lean_dec(v___x_1772_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = l_Lean_Kernel_enableDiag(v_env_1773_, v___x_1725_);
v___x_1785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 5, v___x_1785_);
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_nextMacroScope_1774_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_ngen_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_auxDeclNGen_1776_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_traceState_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_messages_1778_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_infoState_1779_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_snapshotTasks_1780_);
v___x_1787_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_st_ref_put(v___y_1615_, v___x_1787_);
v_fileName_1727_ = v_fileName_1708_;
v_fileMap_1728_ = v_fileMap_1709_;
v_currRecDepth_1729_ = v_currRecDepth_1711_;
v_ref_1730_ = v_ref_1712_;
v_currNamespace_1731_ = v_currNamespace_1713_;
v_openDecls_1732_ = v_openDecls_1714_;
v_initHeartbeats_1733_ = v_initHeartbeats_1715_;
v_maxHeartbeats_1734_ = v_maxHeartbeats_1716_;
v_quotContext_1735_ = v_quotContext_1717_;
v_currMacroScope_1736_ = v_currMacroScope_1718_;
v_cancelTk_x3f_1737_ = v_cancelTk_x3f_1719_;
v_suppressElabErrors_1738_ = v_suppressElabErrors_1720_;
v_inheritedTraceOptions_1739_ = v_inheritedTraceOptions_1721_;
v___y_1740_ = v___y_1615_;
goto v___jp_1726_;
}
}
}
else
{
v_fileName_1727_ = v_fileName_1708_;
v_fileMap_1728_ = v_fileMap_1709_;
v_currRecDepth_1729_ = v_currRecDepth_1711_;
v_ref_1730_ = v_ref_1712_;
v_currNamespace_1731_ = v_currNamespace_1713_;
v_openDecls_1732_ = v_openDecls_1714_;
v_initHeartbeats_1733_ = v_initHeartbeats_1715_;
v_maxHeartbeats_1734_ = v_maxHeartbeats_1716_;
v_quotContext_1735_ = v_quotContext_1717_;
v_currMacroScope_1736_ = v_currMacroScope_1718_;
v_cancelTk_x3f_1737_ = v_cancelTk_x3f_1719_;
v_suppressElabErrors_1738_ = v_suppressElabErrors_1720_;
v_inheritedTraceOptions_1739_ = v_inheritedTraceOptions_1721_;
v___y_1740_ = v___y_1615_;
goto v___jp_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object* v_s_1793_, lean_object* v___f_1794_, lean_object* v___x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___x_12756__boxed_1801_; lean_object* v_res_1802_; 
v___x_12756__boxed_1801_ = lean_unbox(v___x_1795_);
v_res_1802_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(v_s_1793_, v___f_1794_, v___x_12756__boxed_1801_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
return v_res_1802_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1));
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14));
v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16));
v___x_1830_ = l_Lean_stringToMessageData(v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18));
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
return v___x_1833_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34));
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36));
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38));
v___x_1864_ = l_Lean_stringToMessageData(v___x_1863_);
return v___x_1864_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40));
v___x_1867_ = l_Lean_stringToMessageData(v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44));
v___x_1872_ = l_Lean_stringToMessageData(v___x_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46));
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* v_tacticName_1876_, lean_object* v_expectedType_1877_, lean_object* v_s_1878_, lean_object* v_r_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__14));
v___x_1886_ = l_Lean_Expr_isConstOf(v_r_1879_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___f_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v_expectedType_1877_);
v___f_1887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0));
v___x_1888_ = 1;
v___x_1889_ = lean_box(v___x_1888_);
lean_inc_ref(v_s_1878_);
v___f_1890_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1890_, 0, v_s_1878_);
lean_closure_set(v___f_1890_, 1, v___f_1887_);
lean_closure_set(v___f_1890_, 2, v___x_1889_);
v___x_1891_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v___f_1890_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_2005_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_2005_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_2005_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_2004_; 
v_fst_1923_ = lean_ctor_get(v_a_1892_, 0);
v_snd_1924_ = lean_ctor_get(v_a_1892_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_a_1892_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1926_ = v_a_1892_;
v_isShared_1927_ = v_isSharedCheck_2004_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_snd_1924_);
lean_inc(v_fst_1923_);
lean_dec(v_a_1892_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_2004_;
goto v_resetjp_1925_;
}
v___jp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1899_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1900_ = l_Lean_MessageData_ofName(v_tacticName_1876_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_Expr_setPPExplicit(v_s_1878_, v___x_1888_);
v___x_1905_ = l_Lean_indentExpr(v___x_1904_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1903_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12));
v___x_1910_ = l_Lean_MessageData_ofConstName(v___x_1909_, v___x_1886_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1908_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_MessageData_ofConstName(v___x_1885_, v___x_1886_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___y_1897_);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___y_1898_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1919_);
v___x_1921_ = v___x_1894_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
v_resetjp_1925_:
{
lean_object* v___y_1929_; lean_object* v___y_1981_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = lean_array_get_size(v_snd_1924_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_nat_dec_eq(v___x_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = lean_nat_dec_eq(v___x_1994_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42));
v___y_1981_ = v___x_1999_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43));
v___y_1981_ = v___x_2000_;
goto v___jp_1980_;
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec(v_snd_1924_);
v___x_2001_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45);
lean_inc(v_fst_1923_);
v___x_2002_ = l_Lean_indentExpr(v_fst_1923_);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___y_1929_ = v___x_2003_;
goto v___jp_1928_;
}
v___jp_1928_:
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10));
v___x_1931_ = l_Lean_Expr_isAppOf(v_fst_1923_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13));
v___x_1933_ = l_Lean_Expr_isAppOf(v_fst_1923_, v___x_1932_);
lean_dec(v_fst_1923_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_del_object(v___x_1926_);
v___x_1934_ = l_Lean_MessageData_nil;
v___y_1897_ = v___y_1929_;
v___y_1898_ = v___x_1934_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15);
v___x_1936_ = l_Lean_MessageData_ofConstName(v___x_1932_, v___x_1886_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 7);
lean_ctor_set(v___x_1926_, 1, v___x_1936_);
lean_ctor_set(v___x_1926_, 0, v___x_1935_);
v___x_1938_ = v___x_1926_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_1942_ = l_Lean_MessageData_ofConstName(v___x_1941_, v___x_1886_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1940_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
lean_inc(v_tacticName_1876_);
v___x_1946_ = l_Lean_MessageData_ofName(v_tacticName_1876_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23));
v___x_1951_ = l_Lean_MessageData_ofConstName(v___x_1950_, v___x_1886_);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1949_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg___closed__15);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = l_Lean_MessageData_hint_x27(v___x_1954_);
v___y_1897_ = v___y_1929_;
v___y_1898_ = v___x_1955_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_dec(v_fst_1923_);
v___x_1957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25);
v___x_1958_ = l_Lean_MessageData_ofConstName(v___x_1930_, v___x_1886_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 7);
lean_ctor_set(v___x_1926_, 1, v___x_1958_);
lean_ctor_set(v___x_1926_, 0, v___x_1957_);
v___x_1960_ = v___x_1926_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_1964_ = l_Lean_MessageData_ofConstName(v___x_1963_, v___x_1886_);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1962_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31));
v___x_1969_ = l_Lean_MessageData_ofConstName(v___x_1968_, v___x_1886_);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1967_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1970_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33));
v___x_1974_ = l_Lean_MessageData_ofConstName(v___x_1973_, v___x_1886_);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_MessageData_hint_x27(v___x_1977_);
v___y_1897_ = v___y_1929_;
v___y_1898_ = v___x_1978_;
goto v___jp_1896_;
}
}
}
v___jp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1982_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37);
lean_inc_ref(v___y_1981_);
v___x_1983_ = l_Lean_stringToMessageData(v___y_1981_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_array_to_list(v_snd_1924_);
v___x_1988_ = l_Lean_MessageData_andList(v___x_1987_);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
lean_inc(v_fst_1923_);
v___x_1992_ = l_Lean_indentExpr(v_fst_1923_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___y_1929_ = v___x_1993_;
goto v___jp_1928_;
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref(v_s_1878_);
lean_dec(v_tacticName_1876_);
v_a_2006_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1891_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1891_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v_s_1878_);
v___x_2014_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2015_ = l_Lean_MessageData_ofName(v_tacticName_1876_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47);
v___x_2018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2016_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = l_Lean_indentExpr(v_expectedType_1877_);
v___x_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2018_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object* v_tacticName_2024_, lean_object* v_expectedType_2025_, lean_object* v_s_2026_, lean_object* v_r_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_2024_, v_expectedType_2025_, v_s_2026_, v_r_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec_ref(v_r_2027_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object* v_00_u03c3_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_map_2036_, lean_object* v_f_2037_, lean_object* v_init_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(v_map_2036_, v_f_2037_, v_init_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object* v_00_u03c3_2040_, lean_object* v_00_u03b2_2041_, lean_object* v_map_2042_, lean_object* v_f_2043_, lean_object* v_init_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v_00_u03c3_2040_, v_00_u03b2_2041_, v_map_2042_, v_f_2043_, v_init_2044_);
lean_dec_ref(v_map_2042_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object* v_n_2046_, lean_object* v_as_2047_, lean_object* v_lo_2048_, lean_object* v_hi_2049_, lean_object* v_w_2050_, lean_object* v_hlo_2051_, lean_object* v_hhi_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_n_2046_, v_as_2047_, v_lo_2048_, v_hi_2049_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object* v_n_2054_, lean_object* v_as_2055_, lean_object* v_lo_2056_, lean_object* v_hi_2057_, lean_object* v_w_2058_, lean_object* v_hlo_2059_, lean_object* v_hhi_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_n_2054_, v_as_2055_, v_lo_2056_, v_hi_2057_, v_w_2058_, v_hlo_2059_, v_hhi_2060_);
lean_dec(v_hi_2057_);
lean_dec(v_n_2054_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg(lean_object* v_map_2062_, lean_object* v_f_2063_, lean_object* v_init_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_2063_, v_map_2062_, v_init_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg___boxed(lean_object* v_map_2066_, lean_object* v_f_2067_, lean_object* v_init_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg(v_map_2066_, v_f_2067_, v_init_2068_);
lean_dec_ref(v_map_2066_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(lean_object* v_00_u03c3_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_map_2072_, lean_object* v_f_2073_, lean_object* v_init_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_2073_, v_map_2072_, v_init_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2076_, lean_object* v_00_u03b2_2077_, lean_object* v_map_2078_, lean_object* v_f_2079_, lean_object* v_init_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(v_00_u03c3_2076_, v_00_u03b2_2077_, v_map_2078_, v_f_2079_, v_init_2080_);
lean_dec_ref(v_map_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(lean_object* v_n_2082_, lean_object* v_lo_2083_, lean_object* v_hi_2084_, lean_object* v_hhi_2085_, lean_object* v_pivot_2086_, lean_object* v_as_2087_, lean_object* v_i_2088_, lean_object* v_k_2089_, lean_object* v_ilo_2090_, lean_object* v_ik_2091_, lean_object* v_w_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(v_hi_2084_, v_pivot_2086_, v_as_2087_, v_i_2088_, v_k_2089_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___boxed(lean_object* v_n_2094_, lean_object* v_lo_2095_, lean_object* v_hi_2096_, lean_object* v_hhi_2097_, lean_object* v_pivot_2098_, lean_object* v_as_2099_, lean_object* v_i_2100_, lean_object* v_k_2101_, lean_object* v_ilo_2102_, lean_object* v_ik_2103_, lean_object* v_w_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(v_n_2094_, v_lo_2095_, v_hi_2096_, v_hhi_2097_, v_pivot_2098_, v_as_2099_, v_i_2100_, v_k_2101_, v_ilo_2102_, v_ik_2103_, v_w_2104_);
lean_dec(v_pivot_2098_);
lean_dec(v_hi_2096_);
lean_dec(v_lo_2095_);
lean_dec(v_n_2094_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6(lean_object* v_00_u03b1_2106_, lean_object* v_constName_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___redArg(v_constName_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_constName_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6(v_00_u03b1_2114_, v_constName_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10(lean_object* v_00_u03c3_2122_, lean_object* v_00_u03b1_2123_, lean_object* v_00_u03b2_2124_, lean_object* v_f_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_2125_, v_x_2126_, v_x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03c3_2129_, lean_object* v_00_u03b1_2130_, lean_object* v_00_u03b2_2131_, lean_object* v_f_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10(v_00_u03c3_2129_, v_00_u03b1_2130_, v_00_u03b2_2131_, v_f_2132_, v_x_2133_, v_x_2134_);
lean_dec_ref(v_x_2133_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10(lean_object* v_00_u03b1_2136_, lean_object* v_ref_2137_, lean_object* v_constName_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg(v_ref_2137_, v_constName_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_ref_2146_, lean_object* v_constName_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10(v_00_u03b1_2145_, v_ref_2146_, v_constName_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v_ref_2146_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14(lean_object* v_00_u03b1_2154_, lean_object* v_00_u03b2_2155_, lean_object* v_00_u03c3_2156_, lean_object* v_f_2157_, lean_object* v_as_2158_, size_t v_i_2159_, size_t v_stop_2160_, lean_object* v_b_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_2157_, v_as_2158_, v_i_2159_, v_stop_2160_, v_b_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_00_u03c3_2165_, lean_object* v_f_2166_, lean_object* v_as_2167_, lean_object* v_i_2168_, lean_object* v_stop_2169_, lean_object* v_b_2170_){
_start:
{
size_t v_i_boxed_2171_; size_t v_stop_boxed_2172_; lean_object* v_res_2173_; 
v_i_boxed_2171_ = lean_unbox_usize(v_i_2168_);
lean_dec(v_i_2168_);
v_stop_boxed_2172_ = lean_unbox_usize(v_stop_2169_);
lean_dec(v_stop_2169_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14(v_00_u03b1_2163_, v_00_u03b2_2164_, v_00_u03c3_2165_, v_f_2166_, v_as_2167_, v_i_boxed_2171_, v_stop_boxed_2172_, v_b_2170_);
lean_dec_ref(v_as_2167_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15(lean_object* v_00_u03c3_2174_, lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_f_2177_, lean_object* v_keys_2178_, lean_object* v_vals_2179_, lean_object* v_heq_2180_, lean_object* v_i_2181_, lean_object* v_acc_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(v_f_2177_, v_keys_2178_, v_vals_2179_, v_i_2181_, v_acc_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03c3_2184_, lean_object* v_00_u03b1_2185_, lean_object* v_00_u03b2_2186_, lean_object* v_f_2187_, lean_object* v_keys_2188_, lean_object* v_vals_2189_, lean_object* v_heq_2190_, lean_object* v_i_2191_, lean_object* v_acc_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15(v_00_u03c3_2184_, v_00_u03b1_2185_, v_00_u03b2_2186_, v_f_2187_, v_keys_2188_, v_vals_2189_, v_heq_2190_, v_i_2191_, v_acc_2192_);
lean_dec_ref(v_vals_2189_);
lean_dec_ref(v_keys_2188_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15(lean_object* v_00_u03b1_2194_, lean_object* v_ref_2195_, lean_object* v_msg_2196_, lean_object* v_declHint_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___redArg(v_ref_2195_, v_msg_2196_, v_declHint_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b1_2204_, lean_object* v_ref_2205_, lean_object* v_msg_2206_, lean_object* v_declHint_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15(v_00_u03b1_2204_, v_ref_2205_, v_msg_2206_, v_declHint_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v_ref_2205_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20(lean_object* v_msg_2214_, lean_object* v_declHint_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_2214_, v_declHint_2215_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20___boxed(lean_object* v_msg_2222_, lean_object* v_declHint_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__17_spec__20(v_msg_2222_, v_declHint_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18(lean_object* v_00_u03b1_2230_, lean_object* v_ref_2231_, lean_object* v_msg_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___redArg(v_ref_2231_, v_msg_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_ref_2240_, lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18(v_00_u03b1_2239_, v_ref_2240_, v_msg_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v_ref_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22(lean_object* v_00_u03b1_2248_, lean_object* v_msg_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_msg_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22(v_00_u03b1_2256_, v_msg_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2263_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = l_Lean_Level_ofNat(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___x_2268_);
return v___x_2270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2);
v___x_2272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__0));
v___x_2273_ = l_Lean_mkConst(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2));
v___x_2276_ = l_Lean_mkConst(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12));
v___x_2279_ = l_Lean_mkConst(v___x_2278_, v___x_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object* v_tacticName_2280_, lean_object* v_expectedType_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v___x_2287_; 
lean_inc_ref(v_expectedType_2281_);
v___x_2287_ = l_Lean_Meta_mkDecide(v_expectedType_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; uint8_t v_transparency_2290_; lean_object* v___x_2291_; uint8_t v___y_2293_; uint8_t v___x_2332_; uint8_t v___x_2333_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l_Lean_Meta_Context_config(v_a_2282_);
v_transparency_2290_ = lean_ctor_get_uint8(v___x_2289_, 9);
lean_dec_ref(v___x_2289_);
v___x_2291_ = l_Lean_Expr_appArg_x21(v_a_2288_);
v___x_2332_ = 1;
v___x_2333_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2290_, v___x_2332_);
if (v___x_2333_ == 0)
{
v___y_2293_ = v_transparency_2290_;
goto v___jp_2292_;
}
else
{
v___y_2293_ = v___x_2332_;
goto v___jp_2292_;
}
v___jp_2292_:
{
lean_object* v_keyedConfig_2294_; uint8_t v_trackZetaDelta_2295_; lean_object* v_zetaDeltaSet_2296_; lean_object* v_lctx_2297_; lean_object* v_localInstances_2298_; lean_object* v_defEqCtx_x3f_2299_; lean_object* v_synthPendingDepth_2300_; lean_object* v_customCanUnfoldPredicate_x3f_2301_; uint8_t v_univApprox_2302_; uint8_t v_inTypeClassResolution_2303_; uint8_t v_cacheInferType_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_keyedConfig_2294_ = lean_ctor_get(v_a_2282_, 0);
v_trackZetaDelta_2295_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7);
v_zetaDeltaSet_2296_ = lean_ctor_get(v_a_2282_, 1);
v_lctx_2297_ = lean_ctor_get(v_a_2282_, 2);
v_localInstances_2298_ = lean_ctor_get(v_a_2282_, 3);
v_defEqCtx_x3f_2299_ = lean_ctor_get(v_a_2282_, 4);
v_synthPendingDepth_2300_ = lean_ctor_get(v_a_2282_, 5);
v_customCanUnfoldPredicate_x3f_2301_ = lean_ctor_get(v_a_2282_, 6);
v_univApprox_2302_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2303_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7 + 2);
v_cacheInferType_2304_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2294_);
v___x_2305_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2293_, v_keyedConfig_2294_);
lean_inc(v_customCanUnfoldPredicate_x3f_2301_);
lean_inc(v_synthPendingDepth_2300_);
lean_inc(v_defEqCtx_x3f_2299_);
lean_inc_ref(v_localInstances_2298_);
lean_inc_ref(v_lctx_2297_);
lean_inc(v_zetaDeltaSet_2296_);
v___x_2306_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v_zetaDeltaSet_2296_);
lean_ctor_set(v___x_2306_, 2, v_lctx_2297_);
lean_ctor_set(v___x_2306_, 3, v_localInstances_2298_);
lean_ctor_set(v___x_2306_, 4, v_defEqCtx_x3f_2299_);
lean_ctor_set(v___x_2306_, 5, v_synthPendingDepth_2300_);
lean_ctor_set(v___x_2306_, 6, v_customCanUnfoldPredicate_x3f_2301_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*7, v_trackZetaDelta_2295_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*7 + 1, v_univApprox_2302_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2303_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*7 + 3, v_cacheInferType_2304_);
lean_inc(v_a_2285_);
lean_inc_ref(v_a_2284_);
lean_inc(v_a_2283_);
lean_inc(v_a_2288_);
v___x_2307_ = lean_whnf(v_a_2288_, v___x_2306_, v_a_2283_, v_a_2284_, v_a_2285_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2331_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2331_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2331_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12));
v___x_2313_ = l_Lean_Expr_isConstOf(v_a_2308_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_del_object(v___x_2310_);
lean_dec_ref(v___x_2291_);
lean_inc_ref(v_expectedType_2281_);
v___x_2314_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed), 9, 4);
lean_closure_set(v___x_2314_, 0, v_tacticName_2280_);
lean_closure_set(v___x_2314_, 1, v_expectedType_2281_);
lean_closure_set(v___x_2314_, 2, v_a_2288_);
lean_closure_set(v___x_2314_, 3, v_a_2308_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = lean_array_push(v___x_2316_, v_expectedType_2281_);
v___x_2318_ = l_Lean_MessageData_ofLazyM(v___x_2314_, v___x_2317_);
v___x_2319_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2318_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
return v___x_2319_;
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_dec(v_a_2308_);
lean_dec(v_tacticName_2280_);
v___x_2320_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3);
v___x_2321_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4);
v___x_2322_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5);
v___x_2323_ = l_Lean_mkApp3(v___x_2320_, v___x_2321_, v_a_2288_, v___x_2322_);
v___x_2324_ = l_Lean_reflBoolTrue;
v___x_2325_ = l_Lean_Meta_mkExpectedPropHint(v___x_2324_, v___x_2323_);
v___x_2326_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_2327_ = l_Lean_mkApp3(v___x_2326_, v_expectedType_2281_, v___x_2291_, v___x_2325_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2327_);
v___x_2329_ = v___x_2310_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_dec_ref(v___x_2291_);
lean_dec(v_a_2288_);
lean_dec_ref(v_expectedType_2281_);
lean_dec(v_tacticName_2280_);
return v___x_2307_;
}
}
}
else
{
lean_dec_ref(v_expectedType_2281_);
lean_dec(v_tacticName_2280_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(lean_object* v_tacticName_2334_, lean_object* v_expectedType_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2334_, v_expectedType_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* v_tacticName_2342_, lean_object* v_expectedType_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2342_, v_expectedType_2343_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* v_tacticName_2354_, lean_object* v_expectedType_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(v_tacticName_2354_, v_expectedType_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2365_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0));
v___x_2368_ = l_Lean_stringToMessageData(v___x_2367_);
return v___x_2368_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object* v_a_2372_, lean_object* v___x_2373_, lean_object* v_tacticName_2374_, lean_object* v_expectedType_2375_, lean_object* v___x_2376_, uint8_t v___x_2377_, uint8_t v___x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___y_2385_; lean_object* v_a_2386_; uint8_t v___y_2391_; lean_object* v___x_2439_; uint8_t v_transparency_2440_; uint8_t v___x_2441_; 
v___x_2439_ = l_Lean_Meta_Context_config(v___y_2379_);
v_transparency_2440_ = lean_ctor_get_uint8(v___x_2439_, 9);
lean_dec_ref(v___x_2439_);
v___x_2441_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2440_, v___x_2378_);
if (v___x_2441_ == 0)
{
v___y_2391_ = v_transparency_2440_;
goto v___jp_2390_;
}
else
{
v___y_2391_ = v___x_2378_;
goto v___jp_2390_;
}
v___jp_2384_:
{
uint8_t v___x_2387_; 
v___x_2387_ = l_Lean_Exception_isInterrupt(v_a_2386_);
lean_dec_ref(v_a_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v___y_2385_);
v___x_2388_ = l_Lean_Exception_toMessageData(v_a_2372_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
else
{
lean_dec_ref(v_a_2372_);
return v___y_2385_;
}
}
v___jp_2390_:
{
lean_object* v_keyedConfig_2392_; uint8_t v_trackZetaDelta_2393_; lean_object* v_zetaDeltaSet_2394_; lean_object* v_lctx_2395_; lean_object* v_localInstances_2396_; lean_object* v_defEqCtx_x3f_2397_; lean_object* v_synthPendingDepth_2398_; lean_object* v_customCanUnfoldPredicate_x3f_2399_; uint8_t v_univApprox_2400_; uint8_t v_inTypeClassResolution_2401_; uint8_t v_cacheInferType_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_keyedConfig_2392_ = lean_ctor_get(v___y_2379_, 0);
v_trackZetaDelta_2393_ = lean_ctor_get_uint8(v___y_2379_, sizeof(void*)*7);
v_zetaDeltaSet_2394_ = lean_ctor_get(v___y_2379_, 1);
v_lctx_2395_ = lean_ctor_get(v___y_2379_, 2);
v_localInstances_2396_ = lean_ctor_get(v___y_2379_, 3);
v_defEqCtx_x3f_2397_ = lean_ctor_get(v___y_2379_, 4);
v_synthPendingDepth_2398_ = lean_ctor_get(v___y_2379_, 5);
v_customCanUnfoldPredicate_x3f_2399_ = lean_ctor_get(v___y_2379_, 6);
v_univApprox_2400_ = lean_ctor_get_uint8(v___y_2379_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2401_ = lean_ctor_get_uint8(v___y_2379_, sizeof(void*)*7 + 2);
v_cacheInferType_2402_ = lean_ctor_get_uint8(v___y_2379_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2392_);
v___x_2403_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2391_, v_keyedConfig_2392_);
lean_inc(v_customCanUnfoldPredicate_x3f_2399_);
lean_inc(v_synthPendingDepth_2398_);
lean_inc(v_defEqCtx_x3f_2397_);
lean_inc_ref(v_localInstances_2396_);
lean_inc_ref(v_lctx_2395_);
lean_inc(v_zetaDeltaSet_2394_);
v___x_2404_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_zetaDeltaSet_2394_);
lean_ctor_set(v___x_2404_, 2, v_lctx_2395_);
lean_ctor_set(v___x_2404_, 3, v_localInstances_2396_);
lean_ctor_set(v___x_2404_, 4, v_defEqCtx_x3f_2397_);
lean_ctor_set(v___x_2404_, 5, v_synthPendingDepth_2398_);
lean_ctor_set(v___x_2404_, 6, v_customCanUnfoldPredicate_x3f_2399_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7, v_trackZetaDelta_2393_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 1, v_univApprox_2400_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2401_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 3, v_cacheInferType_2402_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___x_2373_);
v___x_2405_ = lean_whnf(v___x_2373_, v___x_2404_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2430_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2430_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2430_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__12));
v___x_2411_ = l_Lean_Expr_isConstOf(v_a_2406_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_del_object(v___x_2408_);
lean_dec_ref(v___x_2376_);
v___x_2412_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_2374_, v_expectedType_2375_, v___x_2373_, v_a_2406_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec_ref(v___y_2379_);
lean_dec(v_a_2406_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_dec_ref(v_a_2372_);
return v___x_2412_;
}
else
{
lean_object* v_a_2413_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
v___y_2385_ = v___x_2412_;
v_a_2386_ = v_a_2413_;
goto v___jp_2384_;
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
lean_dec(v_a_2406_);
lean_dec_ref(v___y_2379_);
lean_dec_ref(v_expectedType_2375_);
lean_dec_ref(v___x_2373_);
v___x_2414_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2415_ = l_Lean_MessageData_ofName(v_tacticName_2374_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_Name_mkStr1(v___x_2376_);
v___x_2420_ = l_Lean_MessageData_ofConstName(v___x_2419_, v___x_2377_);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2418_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_Exception_toMessageData(v_a_2372_);
v___x_2425_ = l_Lean_indentD(v___x_2424_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2423_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2426_);
v___x_2428_ = v___x_2408_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec_ref(v___y_2379_);
lean_dec_ref(v___x_2376_);
lean_dec_ref(v_expectedType_2375_);
lean_dec(v_tacticName_2374_);
lean_dec_ref(v___x_2373_);
v_a_2431_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2405_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2405_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
lean_inc(v_a_2431_);
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
v___y_2385_ = v___x_2436_;
v_a_2386_ = v_a_2431_;
goto v___jp_2384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object* v_a_2442_, lean_object* v___x_2443_, lean_object* v_tacticName_2444_, lean_object* v_expectedType_2445_, lean_object* v___x_2446_, lean_object* v___x_2447_, lean_object* v___x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_6244__boxed_2454_; uint8_t v___x_6245__boxed_2455_; lean_object* v_res_2456_; 
v___x_6244__boxed_2454_ = lean_unbox(v___x_2447_);
v___x_6245__boxed_2455_ = lean_unbox(v___x_2448_);
v_res_2456_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(v_a_2442_, v___x_2443_, v_tacticName_2444_, v_expectedType_2445_, v___x_2446_, v___x_6244__boxed_2454_, v___x_6245__boxed_2455_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
return v_res_2456_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(lean_object* v_a_2457_, lean_object* v_as_2458_, size_t v_i_2459_, size_t v_stop_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_eq(v_i_2459_, v_stop_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = lean_array_uget_borrowed(v_as_2458_, v_i_2459_);
v___x_2463_ = lean_name_eq(v_a_2457_, v___x_2462_);
if (v___x_2463_ == 0)
{
size_t v___x_2464_; size_t v___x_2465_; 
v___x_2464_ = ((size_t)1ULL);
v___x_2465_ = lean_usize_add(v_i_2459_, v___x_2464_);
v_i_2459_ = v___x_2465_;
goto _start;
}
else
{
return v___x_2463_;
}
}
else
{
uint8_t v___x_2467_; 
v___x_2467_ = 0;
return v___x_2467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(lean_object* v_a_2468_, lean_object* v_as_2469_, lean_object* v_i_2470_, lean_object* v_stop_2471_){
_start:
{
size_t v_i_boxed_2472_; size_t v_stop_boxed_2473_; uint8_t v_res_2474_; lean_object* v_r_2475_; 
v_i_boxed_2472_ = lean_unbox_usize(v_i_2470_);
lean_dec(v_i_2470_);
v_stop_boxed_2473_ = lean_unbox_usize(v_stop_2471_);
lean_dec(v_stop_2471_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2468_, v_as_2469_, v_i_boxed_2472_, v_stop_boxed_2473_);
lean_dec_ref(v_as_2469_);
lean_dec(v_a_2468_);
v_r_2475_ = lean_box(v_res_2474_);
return v_r_2475_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object* v_as_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_array_get_size(v_as_2476_);
v___x_2480_ = lean_nat_dec_lt(v___x_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
return v___x_2480_;
}
else
{
if (v___x_2480_ == 0)
{
return v___x_2480_;
}
else
{
size_t v___x_2481_; size_t v___x_2482_; uint8_t v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2479_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2477_, v_as_2476_, v___x_2481_, v___x_2482_);
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object* v_as_2484_, lean_object* v_a_2485_){
_start:
{
uint8_t v_res_2486_; lean_object* v_r_2487_; 
v_res_2486_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v_as_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_as_2484_);
v_r_2487_ = lean_box(v_res_2486_);
return v_r_2487_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(lean_object* v___x_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
if (lean_obj_tag(v_a_2489_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = l_List_reverse___redArg(v_a_2490_);
return v___x_2491_;
}
else
{
lean_object* v_head_2492_; lean_object* v_tail_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2503_; 
v_head_2492_ = lean_ctor_get(v_a_2489_, 0);
v_tail_2493_ = lean_ctor_get(v_a_2489_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2489_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2495_ = v_a_2489_;
v_isShared_2496_ = v_isSharedCheck_2503_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_tail_2493_);
lean_inc(v_head_2492_);
lean_dec(v_a_2489_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2503_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
uint8_t v___x_2497_; 
v___x_2497_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v___x_2488_, v_head_2492_);
if (v___x_2497_ == 0)
{
lean_del_object(v___x_2495_);
lean_dec(v_head_2492_);
v_a_2489_ = v_tail_2493_;
goto _start;
}
else
{
lean_object* v___x_2500_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v_a_2490_);
v___x_2500_ = v___x_2495_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_head_2492_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_a_2490_);
v___x_2500_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
v_a_2489_ = v_tail_2493_;
v_a_2490_ = v___x_2500_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(lean_object* v___x_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v___x_2504_, v_a_2505_, v_a_2506_);
lean_dec_ref(v___x_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
if (lean_obj_tag(v_a_2508_) == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = l_List_reverse___redArg(v_a_2509_);
return v___x_2510_;
}
else
{
lean_object* v_head_2511_; lean_object* v_tail_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2521_; 
v_head_2511_ = lean_ctor_get(v_a_2508_, 0);
v_tail_2512_ = lean_ctor_get(v_a_2508_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2514_ = v_a_2508_;
v_isShared_2515_ = v_isSharedCheck_2521_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_tail_2512_);
lean_inc(v_head_2511_);
lean_dec(v_a_2508_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2521_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_Level_param___override(v_head_2511_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 1, v_a_2509_);
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_a_2509_);
v___x_2518_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
v_a_2508_ = v_tail_2512_;
v_a_2509_ = v___x_2518_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = lean_unsigned_to_nat(16u);
v___x_2524_ = lean_mk_array(v___x_2523_, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0);
v___x_2526_ = lean_unsigned_to_nat(0u);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2529_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1);
v___x_2530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
lean_ctor_set(v___x_2530_, 2, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4));
v___x_2537_ = l_Lean_mkConst(v___x_2536_, v___x_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object* v_tacticName_2538_, lean_object* v_expectedType_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; 
lean_inc_ref(v_expectedType_2539_);
v___x_2548_ = l_Lean_Meta_mkDecideProof(v_expectedType_2539_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = l_Lean_Elab_Term_getLevelNames___redArg(v_a_2542_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_2540_, v_a_2542_, v_a_2544_, v_a_2546_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2670_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2670_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2670_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_params_2560_; lean_object* v_fileName_2561_; lean_object* v_fileMap_2562_; lean_object* v_options_2563_; lean_object* v_currRecDepth_2564_; lean_object* v_ref_2565_; lean_object* v_currNamespace_2566_; lean_object* v_openDecls_2567_; lean_object* v_initHeartbeats_2568_; lean_object* v_maxHeartbeats_2569_; lean_object* v_quotContext_2570_; lean_object* v_currMacroScope_2571_; lean_object* v_cancelTk_x3f_2572_; uint8_t v_suppressElabErrors_2573_; lean_object* v_inheritedTraceOptions_2574_; lean_object* v_env_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; uint8_t v___x_2583_; lean_object* v___y_2585_; uint8_t v___y_2586_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v_fileName_2616_; lean_object* v_fileMap_2617_; lean_object* v_currRecDepth_2618_; lean_object* v_ref_2619_; lean_object* v_currNamespace_2620_; lean_object* v_openDecls_2621_; lean_object* v_initHeartbeats_2622_; lean_object* v_maxHeartbeats_2623_; lean_object* v_quotContext_2624_; lean_object* v_currMacroScope_2625_; lean_object* v_cancelTk_x3f_2626_; uint8_t v_suppressElabErrors_2627_; lean_object* v_inheritedTraceOptions_2628_; lean_object* v___y_2629_; uint8_t v___y_2648_; uint8_t v___x_2669_; 
v___x_2557_ = lean_st_ref_get(v_a_2546_);
v___x_2558_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2);
lean_inc_ref(v_expectedType_2539_);
v___x_2559_ = l_Lean_collectLevelParams(v___x_2558_, v_expectedType_2539_);
v_params_2560_ = lean_ctor_get(v___x_2559_, 2);
lean_inc_ref(v_params_2560_);
lean_dec_ref(v___x_2559_);
v_fileName_2561_ = lean_ctor_get(v_a_2545_, 0);
v_fileMap_2562_ = lean_ctor_get(v_a_2545_, 1);
v_options_2563_ = lean_ctor_get(v_a_2545_, 2);
v_currRecDepth_2564_ = lean_ctor_get(v_a_2545_, 3);
v_ref_2565_ = lean_ctor_get(v_a_2545_, 5);
v_currNamespace_2566_ = lean_ctor_get(v_a_2545_, 6);
v_openDecls_2567_ = lean_ctor_get(v_a_2545_, 7);
v_initHeartbeats_2568_ = lean_ctor_get(v_a_2545_, 8);
v_maxHeartbeats_2569_ = lean_ctor_get(v_a_2545_, 9);
v_quotContext_2570_ = lean_ctor_get(v_a_2545_, 10);
v_currMacroScope_2571_ = lean_ctor_get(v_a_2545_, 11);
v_cancelTk_x3f_2572_ = lean_ctor_get(v_a_2545_, 12);
v_suppressElabErrors_2573_ = lean_ctor_get_uint8(v_a_2545_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2574_ = lean_ctor_get(v_a_2545_, 13);
v_env_2575_ = lean_ctor_get(v___x_2557_, 0);
lean_inc_ref(v_env_2575_);
lean_dec(v___x_2557_);
v___x_2576_ = l_Lean_Expr_appFn_x21(v_a_2549_);
v___x_2577_ = l_Lean_Expr_appArg_x21(v___x_2576_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = l_List_reverse___redArg(v_a_2551_);
v___x_2579_ = lean_box(0);
v___x_2580_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v_params_2560_, v___x_2578_, v___x_2579_);
lean_dec_ref(v_params_2560_);
v___x_2581_ = lean_box(0);
v___x_2582_ = 1;
v___x_2583_ = 0;
v___x_2611_ = l_Lean_Elab_async;
lean_inc_ref(v_options_2563_);
v___x_2612_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_2563_, v___x_2611_, v___x_2583_);
v___x_2613_ = l_Lean_diagnostics;
v___x_2614_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_2612_, v___x_2613_);
v___x_2669_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2575_);
lean_dec_ref(v_env_2575_);
if (v___x_2669_ == 0)
{
if (v___x_2614_ == 0)
{
v_fileName_2616_ = v_fileName_2561_;
v_fileMap_2617_ = v_fileMap_2562_;
v_currRecDepth_2618_ = v_currRecDepth_2564_;
v_ref_2619_ = v_ref_2565_;
v_currNamespace_2620_ = v_currNamespace_2566_;
v_openDecls_2621_ = v_openDecls_2567_;
v_initHeartbeats_2622_ = v_initHeartbeats_2568_;
v_maxHeartbeats_2623_ = v_maxHeartbeats_2569_;
v_quotContext_2624_ = v_quotContext_2570_;
v_currMacroScope_2625_ = v_currMacroScope_2571_;
v_cancelTk_x3f_2626_ = v_cancelTk_x3f_2572_;
v_suppressElabErrors_2627_ = v_suppressElabErrors_2573_;
v_inheritedTraceOptions_2628_ = v_inheritedTraceOptions_2574_;
v___y_2629_ = v_a_2546_;
goto v___jp_2615_;
}
else
{
v___y_2648_ = v___x_2669_;
goto v___jp_2647_;
}
}
else
{
v___y_2648_ = v___x_2614_;
goto v___jp_2647_;
}
v___jp_2584_:
{
if (v___y_2586_ == 0)
{
lean_object* v___x_2587_; 
lean_del_object(v___x_2555_);
v___x_2587_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2553_, v___y_2586_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref_known(v___x_2587_, 1);
v___x_2588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3));
v___x_2589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5);
lean_inc_ref_n(v_expectedType_2539_, 2);
v___x_2590_ = l_Lean_mkAppB(v___x_2589_, v_expectedType_2539_, v___x_2577_);
v___x_2591_ = 1;
v___x_2592_ = lean_box(v___x_2583_);
v___x_2593_ = lean_box(v___x_2591_);
v___f_2594_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2594_, 0, v___y_2585_);
lean_closure_set(v___f_2594_, 1, v___x_2590_);
lean_closure_set(v___f_2594_, 2, v_tacticName_2538_);
lean_closure_set(v___f_2594_, 3, v_expectedType_2539_);
lean_closure_set(v___f_2594_, 4, v___x_2588_);
lean_closure_set(v___f_2594_, 5, v___x_2592_);
lean_closure_set(v___f_2594_, 6, v___x_2593_);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2595_);
v___x_2597_ = lean_array_push(v___x_2596_, v_expectedType_2539_);
v___x_2598_ = l_Lean_MessageData_ofLazyM(v___f_2594_, v___x_2597_);
v___x_2599_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2598_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
return v___x_2599_;
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___x_2577_);
lean_dec_ref(v_expectedType_2539_);
lean_dec(v_tacticName_2538_);
v_a_2600_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2587_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2587_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v___x_2609_; 
lean_dec_ref(v___x_2577_);
lean_dec(v_a_2553_);
lean_dec_ref(v_expectedType_2539_);
lean_dec(v_tacticName_2538_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 1);
lean_ctor_set(v___x_2555_, 0, v___y_2585_);
v___x_2609_ = v___x_2555_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___y_2585_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
v___jp_2615_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = l_Lean_maxRecDepth;
v___x_2631_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_2612_, v___x_2630_);
lean_inc_ref(v_inheritedTraceOptions_2628_);
lean_inc(v_cancelTk_x3f_2626_);
lean_inc(v_currMacroScope_2625_);
lean_inc(v_quotContext_2624_);
lean_inc(v_maxHeartbeats_2623_);
lean_inc(v_initHeartbeats_2622_);
lean_inc(v_openDecls_2621_);
lean_inc(v_currNamespace_2620_);
lean_inc(v_ref_2619_);
lean_inc(v_currRecDepth_2618_);
lean_inc_ref(v_fileMap_2617_);
lean_inc_ref(v_fileName_2616_);
v___x_2632_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2632_, 0, v_fileName_2616_);
lean_ctor_set(v___x_2632_, 1, v_fileMap_2617_);
lean_ctor_set(v___x_2632_, 2, v___x_2612_);
lean_ctor_set(v___x_2632_, 3, v_currRecDepth_2618_);
lean_ctor_set(v___x_2632_, 4, v___x_2631_);
lean_ctor_set(v___x_2632_, 5, v_ref_2619_);
lean_ctor_set(v___x_2632_, 6, v_currNamespace_2620_);
lean_ctor_set(v___x_2632_, 7, v_openDecls_2621_);
lean_ctor_set(v___x_2632_, 8, v_initHeartbeats_2622_);
lean_ctor_set(v___x_2632_, 9, v_maxHeartbeats_2623_);
lean_ctor_set(v___x_2632_, 10, v_quotContext_2624_);
lean_ctor_set(v___x_2632_, 11, v_currMacroScope_2625_);
lean_ctor_set(v___x_2632_, 12, v_cancelTk_x3f_2626_);
lean_ctor_set(v___x_2632_, 13, v_inheritedTraceOptions_2628_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*14, v___x_2614_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*14 + 1, v_suppressElabErrors_2627_);
lean_inc_ref(v_expectedType_2539_);
lean_inc(v___x_2580_);
v___x_2633_ = l_Lean_Meta_mkAuxLemma(v___x_2580_, v_expectedType_2539_, v_a_2549_, v___x_2581_, v___x_2582_, v___x_2583_, v___x_2583_, v___x_2583_, v_a_2543_, v_a_2544_, v___x_2632_, v___y_2629_);
lean_dec_ref_known(v___x_2632_, 14);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v___x_2577_);
lean_del_object(v___x_2555_);
lean_dec(v_a_2553_);
lean_dec_ref(v_expectedType_2539_);
lean_dec(v_tacticName_2538_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2638_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(v___x_2580_, v___x_2579_);
v___x_2639_ = l_Lean_mkConst(v_a_2634_, v___x_2638_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2644_; uint8_t v___x_2645_; 
lean_dec(v___x_2580_);
v_a_2644_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2645_ = l_Lean_Exception_isInterrupt(v_a_2644_);
if (v___x_2645_ == 0)
{
uint8_t v___x_2646_; 
lean_inc(v_a_2644_);
v___x_2646_ = l_Lean_Exception_isRuntime(v_a_2644_);
v___y_2585_ = v_a_2644_;
v___y_2586_ = v___x_2646_;
goto v___jp_2584_;
}
else
{
v___y_2585_ = v_a_2644_;
v___y_2586_ = v___x_2645_;
goto v___jp_2584_;
}
}
}
v___jp_2647_:
{
if (v___y_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v_env_2650_; lean_object* v_nextMacroScope_2651_; lean_object* v_ngen_2652_; lean_object* v_auxDeclNGen_2653_; lean_object* v_traceState_2654_; lean_object* v_messages_2655_; lean_object* v_infoState_2656_; lean_object* v_snapshotTasks_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2667_; 
v___x_2649_ = lean_st_ref_take(v_a_2546_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
v_nextMacroScope_2651_ = lean_ctor_get(v___x_2649_, 1);
v_ngen_2652_ = lean_ctor_get(v___x_2649_, 2);
v_auxDeclNGen_2653_ = lean_ctor_get(v___x_2649_, 3);
v_traceState_2654_ = lean_ctor_get(v___x_2649_, 4);
v_messages_2655_ = lean_ctor_get(v___x_2649_, 6);
v_infoState_2656_ = lean_ctor_get(v___x_2649_, 7);
v_snapshotTasks_2657_ = lean_ctor_get(v___x_2649_, 8);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2649_, 5);
lean_dec(v_unused_2668_);
v___x_2659_ = v___x_2649_;
v_isShared_2660_ = v_isSharedCheck_2667_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snapshotTasks_2657_);
lean_inc(v_infoState_2656_);
lean_inc(v_messages_2655_);
lean_inc(v_traceState_2654_);
lean_inc(v_auxDeclNGen_2653_);
lean_inc(v_ngen_2652_);
lean_inc(v_nextMacroScope_2651_);
lean_inc(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2667_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2661_ = l_Lean_Kernel_enableDiag(v_env_2650_, v___x_2614_);
v___x_2662_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 5, v___x_2662_);
lean_ctor_set(v___x_2659_, 0, v___x_2661_);
v___x_2664_ = v___x_2659_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_nextMacroScope_2651_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_ngen_2652_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v_auxDeclNGen_2653_);
lean_ctor_set(v_reuseFailAlloc_2666_, 4, v_traceState_2654_);
lean_ctor_set(v_reuseFailAlloc_2666_, 5, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2666_, 6, v_messages_2655_);
lean_ctor_set(v_reuseFailAlloc_2666_, 7, v_infoState_2656_);
lean_ctor_set(v_reuseFailAlloc_2666_, 8, v_snapshotTasks_2657_);
v___x_2664_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_st_ref_put(v_a_2546_, v___x_2664_);
v_fileName_2616_ = v_fileName_2561_;
v_fileMap_2617_ = v_fileMap_2562_;
v_currRecDepth_2618_ = v_currRecDepth_2564_;
v_ref_2619_ = v_ref_2565_;
v_currNamespace_2620_ = v_currNamespace_2566_;
v_openDecls_2621_ = v_openDecls_2567_;
v_initHeartbeats_2622_ = v_initHeartbeats_2568_;
v_maxHeartbeats_2623_ = v_maxHeartbeats_2569_;
v_quotContext_2624_ = v_quotContext_2570_;
v_currMacroScope_2625_ = v_currMacroScope_2571_;
v_cancelTk_x3f_2626_ = v_cancelTk_x3f_2572_;
v_suppressElabErrors_2627_ = v_suppressElabErrors_2573_;
v_inheritedTraceOptions_2628_ = v_inheritedTraceOptions_2574_;
v___y_2629_ = v_a_2546_;
goto v___jp_2615_;
}
}
}
else
{
v_fileName_2616_ = v_fileName_2561_;
v_fileMap_2617_ = v_fileMap_2562_;
v_currRecDepth_2618_ = v_currRecDepth_2564_;
v_ref_2619_ = v_ref_2565_;
v_currNamespace_2620_ = v_currNamespace_2566_;
v_openDecls_2621_ = v_openDecls_2567_;
v_initHeartbeats_2622_ = v_initHeartbeats_2568_;
v_maxHeartbeats_2623_ = v_maxHeartbeats_2569_;
v_quotContext_2624_ = v_quotContext_2570_;
v_currMacroScope_2625_ = v_currMacroScope_2571_;
v_cancelTk_x3f_2626_ = v_cancelTk_x3f_2572_;
v_suppressElabErrors_2627_ = v_suppressElabErrors_2573_;
v_inheritedTraceOptions_2628_ = v_inheritedTraceOptions_2574_;
v___y_2629_ = v_a_2546_;
goto v___jp_2615_;
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v_a_2551_);
lean_dec(v_a_2549_);
lean_dec_ref(v_expectedType_2539_);
lean_dec(v_tacticName_2538_);
v_a_2671_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2552_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2552_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_expectedType_2539_);
lean_dec(v_tacticName_2538_);
v_a_2679_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2550_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2550_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2539_);
lean_dec(v_tacticName_2538_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object* v_tacticName_2687_, lean_object* v_expectedType_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2687_, v_expectedType_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* v_tacticName_2698_, lean_object* v_expectedType_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2698_, v_expectedType_2699_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* v_tacticName_2710_, lean_object* v_expectedType_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(v_tacticName_2710_, v_expectedType_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2721_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0));
v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t v_native_2725_, uint8_t v_kernel_2726_, lean_object* v_tacticName_2727_, lean_object* v_expectedType_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; 
if (v_kernel_2726_ == 0)
{
v___y_2740_ = v___y_2730_;
v___y_2741_ = v___y_2731_;
v___y_2742_ = v___y_2732_;
v___y_2743_ = v___y_2733_;
v___y_2744_ = v___y_2734_;
v___y_2745_ = v___y_2735_;
v___y_2746_ = v___y_2736_;
v___y_2747_ = v___y_2737_;
goto v___jp_2739_;
}
else
{
if (v_native_2725_ == 0)
{
v___y_2740_ = v___y_2730_;
v___y_2741_ = v___y_2731_;
v___y_2742_ = v___y_2732_;
v___y_2743_ = v___y_2733_;
v___y_2744_ = v___y_2734_;
v___y_2745_ = v___y_2735_;
v___y_2746_ = v___y_2736_;
v___y_2747_ = v___y_2737_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v_expectedType_2728_);
v___x_2755_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2756_ = l_Lean_MessageData_ofName(v_tacticName_2727_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_obj_once(&l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1, &l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2759_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
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
v___jp_2739_:
{
lean_object* v___x_2748_; 
v___x_2748_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_2728_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2748_) == 0)
{
if (v_native_2725_ == 0)
{
if (v_kernel_2726_ == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2727_, v_a_2749_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
return v___x_2750_;
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2752_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2727_, v_a_2751_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
return v___x_2752_;
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2754_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_2727_, v_a_2753_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
return v___x_2754_;
}
}
else
{
lean_dec(v_tacticName_2727_);
return v___x_2748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object* v_native_2769_, lean_object* v_kernel_2770_, lean_object* v_tacticName_2771_, lean_object* v_expectedType_2772_, lean_object* v_x_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
uint8_t v_native_boxed_2783_; uint8_t v_kernel_boxed_2784_; lean_object* v_res_2785_; 
v_native_boxed_2783_ = lean_unbox(v_native_2769_);
v_kernel_boxed_2784_ = lean_unbox(v_kernel_2770_);
v_res_2785_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0(v_native_boxed_2783_, v_kernel_boxed_2784_, v_tacticName_2771_, v_expectedType_2772_, v_x_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v_x_2773_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t v_revert_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2788_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2799_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_a_2797_, v___x_2798_, v_revert_2786_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc_n(v_a_2800_, 2);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = l_Lean_MVarId_getDecl(v_a_2800_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v_lctx_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v_lctx_2803_ = lean_ctor_get(v_a_2802_, 1);
lean_inc_ref(v_lctx_2803_);
lean_dec(v_a_2802_);
v___x_2804_ = l_Lean_LocalContext_getFVarIds(v_lctx_2803_);
lean_dec_ref(v_lctx_2803_);
v___x_2805_ = 0;
v___x_2806_ = l_Lean_MVarId_revert(v_a_2800_, v___x_2804_, v___x_2805_, v_revert_2786_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_snd_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2817_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_snd_2808_ = lean_ctor_get(v_a_2807_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2807_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v_a_2807_, 0);
lean_dec(v_unused_2818_);
v___x_2810_ = v_a_2807_;
v_isShared_2811_ = v_isSharedCheck_2817_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_snd_2808_);
lean_dec(v_a_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2817_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_box(0);
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 1);
lean_ctor_set(v___x_2810_, 1, v___x_2812_);
lean_ctor_set(v___x_2810_, 0, v_snd_2808_);
v___x_2814_ = v___x_2810_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_snd_2808_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2814_, v___y_2788_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
return v___x_2815_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
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
lean_dec(v_a_2800_);
v_a_2827_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2801_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2801_);
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
v_a_2835_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2799_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2799_);
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
v_a_2843_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2796_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2796_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object* v_revert_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v_revert_boxed_2861_; lean_object* v_res_2862_; 
v_revert_boxed_2861_ = lean_unbox(v_revert_2851_);
v_res_2862_ = l_Lean_Elab_Tactic_evalDecideCore___lam__1(v_revert_boxed_2861_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* v_tacticName_2863_, lean_object* v_cfg_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
uint8_t v_kernel_2874_; uint8_t v_native_2875_; uint8_t v_revert_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___f_2879_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; 
v_kernel_2874_ = lean_ctor_get_uint8(v_cfg_2864_, 0);
v_native_2875_ = lean_ctor_get_uint8(v_cfg_2864_, 1);
v_revert_2876_ = lean_ctor_get_uint8(v_cfg_2864_, 3);
v___x_2877_ = lean_box(v_native_2875_);
v___x_2878_ = lean_box(v_kernel_2874_);
lean_inc(v_tacticName_2863_);
v___f_2879_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2879_, 0, v___x_2877_);
lean_closure_set(v___f_2879_, 1, v___x_2878_);
lean_closure_set(v___f_2879_, 2, v_tacticName_2863_);
if (v_revert_2876_ == 0)
{
v___y_2881_ = v_a_2865_;
v___y_2882_ = v_a_2866_;
v___y_2883_ = v_a_2867_;
v___y_2884_ = v_a_2868_;
v___y_2885_ = v_a_2869_;
v___y_2886_ = v_a_2870_;
v___y_2887_ = v_a_2871_;
v___y_2888_ = v_a_2872_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2891_; lean_object* v___f_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_box(v_revert_2876_);
v___f_2892_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2892_, 0, v___x_2891_);
v___x_2893_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2892_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_dec_ref_known(v___x_2893_, 1);
v___y_2881_ = v_a_2865_;
v___y_2882_ = v_a_2866_;
v___y_2883_ = v_a_2867_;
v___y_2884_ = v_a_2868_;
v___y_2885_ = v_a_2869_;
v___y_2886_ = v_a_2870_;
v___y_2887_ = v_a_2871_;
v___y_2888_ = v_a_2872_;
goto v___jp_2880_;
}
else
{
lean_dec_ref(v___f_2879_);
lean_dec(v_tacticName_2863_);
return v___x_2893_;
}
}
v___jp_2880_:
{
uint8_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = 1;
v___x_2890_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacticName_2863_, v___f_2879_, v___x_2889_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object* v_tacticName_2894_, lean_object* v_cfg_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Elab_Tactic_evalDecideCore(v_tacticName_2894_, v_cfg_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v_cfg_2895_);
return v_res_2905_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2906_ = lean_box(0);
v___x_2907_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___x_2906_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(v_00_u03b1_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2927_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1));
v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(lean_object* v_ctor_2932_, lean_object* v_args_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0));
v___x_3002_ = lean_string_dec_eq(v_ctor_2932_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3004_ = lean_array_get_size(v_args_2933_);
v___x_3005_ = lean_unsigned_to_nat(4u);
v___x_3006_ = lean_nat_dec_eq(v___x_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v___x_3007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2);
v___x_3008_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10_spec__15_spec__18_spec__22___redArg(v___x_3007_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
goto v___jp_2939_;
}
}
v___jp_2939_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = l_Lean_instInhabitedExpr;
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = lean_array_get_borrowed(v___x_2940_, v_args_2933_, v___x_2941_);
lean_inc(v___x_2942_);
v___x_2943_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2942_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = lean_unsigned_to_nat(1u);
v___x_2946_ = lean_array_get_borrowed(v___x_2940_, v_args_2933_, v___x_2945_);
lean_inc(v___x_2946_);
v___x_2947_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2946_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = lean_unsigned_to_nat(2u);
v___x_2950_ = lean_array_get_borrowed(v___x_2940_, v_args_2933_, v___x_2949_);
lean_inc(v___x_2950_);
v___x_2951_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2950_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = lean_unsigned_to_nat(3u);
v___x_2954_ = lean_array_get_borrowed(v___x_2940_, v_args_2933_, v___x_2953_);
lean_inc(v___x_2954_);
v___x_2955_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2954_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2968_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2968_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2968_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; uint8_t v___x_2962_; uint8_t v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2966_; 
v___x_2960_ = lean_alloc_ctor(0, 0, 4);
v___x_2961_ = lean_unbox(v_a_2944_);
lean_dec(v_a_2944_);
lean_ctor_set_uint8(v___x_2960_, 0, v___x_2961_);
v___x_2962_ = lean_unbox(v_a_2948_);
lean_dec(v_a_2948_);
lean_ctor_set_uint8(v___x_2960_, 1, v___x_2962_);
v___x_2963_ = lean_unbox(v_a_2952_);
lean_dec(v_a_2952_);
lean_ctor_set_uint8(v___x_2960_, 2, v___x_2963_);
v___x_2964_ = lean_unbox(v_a_2956_);
lean_dec(v_a_2956_);
lean_ctor_set_uint8(v___x_2960_, 3, v___x_2964_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2960_);
v___x_2966_ = v___x_2958_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2960_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_a_2952_);
lean_dec(v_a_2948_);
lean_dec(v_a_2944_);
v_a_2969_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2955_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2955_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_a_2948_);
lean_dec(v_a_2944_);
v_a_2977_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2951_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2951_);
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
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_a_2944_);
v_a_2985_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2947_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2947_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2993_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2943_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2943_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed(lean_object* v_ctor_3017_, lean_object* v_args_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(v_ctor_3017_, v_args_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v_args_3018_);
lean_dec_ref(v_ctor_3017_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___f_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___f_3041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0));
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3043_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_3042_, v___f_3041_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed(lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
return v_res_3050_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_box(0);
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3054_ = l_Lean_Expr_const___override(v___x_3053_, v___x_3052_);
return v___x_3054_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0));
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig(void){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = l_Lean_Elab_abortTermExceptionId;
v___x_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0);
v___x_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
return v_res_3068_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0));
v___x_3071_ = l_Lean_stringToMessageData(v___x_3070_);
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
v___x_3073_ = l_Lean_MessageData_ofExpr(v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2);
v___x_3075_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__6_spec__10___redArg___closed__3);
v___x_3078_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5));
v___x_3082_ = l_Lean_stringToMessageData(v___x_3081_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7));
v___x_3085_ = l_Lean_stringToMessageData(v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v_ty_x3f_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v_fileName_3100_; lean_object* v_fileMap_3101_; lean_object* v_options_3102_; lean_object* v_currRecDepth_3103_; lean_object* v_maxRecDepth_3104_; lean_object* v_ref_3105_; lean_object* v_currNamespace_3106_; lean_object* v_openDecls_3107_; lean_object* v_initHeartbeats_3108_; lean_object* v_maxHeartbeats_3109_; lean_object* v_quotContext_3110_; lean_object* v_currMacroScope_3111_; uint8_t v_diag_3112_; lean_object* v_cancelTk_x3f_3113_; uint8_t v_suppressElabErrors_3114_; lean_object* v_inheritedTraceOptions_3115_; uint8_t v___x_3116_; lean_object* v_ref_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_ty_x3f_3094_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
v___x_3095_ = 1;
v___x_3096_ = lean_box(0);
v___x_3097_ = lean_box(v___x_3095_);
v___x_3098_ = lean_box(v___x_3095_);
lean_inc(v_stx_3086_);
v___x_3099_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3099_, 0, v_stx_3086_);
lean_closure_set(v___x_3099_, 1, v_ty_x3f_3094_);
lean_closure_set(v___x_3099_, 2, v___x_3097_);
lean_closure_set(v___x_3099_, 3, v___x_3098_);
lean_closure_set(v___x_3099_, 4, v___x_3096_);
v_fileName_3100_ = lean_ctor_get(v_a_3091_, 0);
v_fileMap_3101_ = lean_ctor_get(v_a_3091_, 1);
v_options_3102_ = lean_ctor_get(v_a_3091_, 2);
v_currRecDepth_3103_ = lean_ctor_get(v_a_3091_, 3);
v_maxRecDepth_3104_ = lean_ctor_get(v_a_3091_, 4);
v_ref_3105_ = lean_ctor_get(v_a_3091_, 5);
v_currNamespace_3106_ = lean_ctor_get(v_a_3091_, 6);
v_openDecls_3107_ = lean_ctor_get(v_a_3091_, 7);
v_initHeartbeats_3108_ = lean_ctor_get(v_a_3091_, 8);
v_maxHeartbeats_3109_ = lean_ctor_get(v_a_3091_, 9);
v_quotContext_3110_ = lean_ctor_get(v_a_3091_, 10);
v_currMacroScope_3111_ = lean_ctor_get(v_a_3091_, 11);
v_diag_3112_ = lean_ctor_get_uint8(v_a_3091_, sizeof(void*)*14);
v_cancelTk_x3f_3113_ = lean_ctor_get(v_a_3091_, 12);
v_suppressElabErrors_3114_ = lean_ctor_get_uint8(v_a_3091_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3115_ = lean_ctor_get(v_a_3091_, 13);
v___x_3116_ = 1;
v_ref_3117_ = l_Lean_replaceRef(v_stx_3086_, v_ref_3105_);
lean_dec(v_stx_3086_);
lean_inc_ref(v_inheritedTraceOptions_3115_);
lean_inc(v_cancelTk_x3f_3113_);
lean_inc(v_currMacroScope_3111_);
lean_inc(v_quotContext_3110_);
lean_inc(v_maxHeartbeats_3109_);
lean_inc(v_initHeartbeats_3108_);
lean_inc(v_openDecls_3107_);
lean_inc(v_currNamespace_3106_);
lean_inc(v_maxRecDepth_3104_);
lean_inc(v_currRecDepth_3103_);
lean_inc_ref(v_options_3102_);
lean_inc_ref(v_fileMap_3101_);
lean_inc_ref(v_fileName_3100_);
v___x_3118_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3118_, 0, v_fileName_3100_);
lean_ctor_set(v___x_3118_, 1, v_fileMap_3101_);
lean_ctor_set(v___x_3118_, 2, v_options_3102_);
lean_ctor_set(v___x_3118_, 3, v_currRecDepth_3103_);
lean_ctor_set(v___x_3118_, 4, v_maxRecDepth_3104_);
lean_ctor_set(v___x_3118_, 5, v_ref_3117_);
lean_ctor_set(v___x_3118_, 6, v_currNamespace_3106_);
lean_ctor_set(v___x_3118_, 7, v_openDecls_3107_);
lean_ctor_set(v___x_3118_, 8, v_initHeartbeats_3108_);
lean_ctor_set(v___x_3118_, 9, v_maxHeartbeats_3109_);
lean_ctor_set(v___x_3118_, 10, v_quotContext_3110_);
lean_ctor_set(v___x_3118_, 11, v_currMacroScope_3111_);
lean_ctor_set(v___x_3118_, 12, v_cancelTk_x3f_3113_);
lean_ctor_set(v___x_3118_, 13, v_inheritedTraceOptions_3115_);
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*14, v_diag_3112_);
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*14 + 1, v_suppressElabErrors_3114_);
v___x_3119_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3099_, v___x_3116_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v___x_3118_, v_a_3092_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; lean_object* v_a_3122_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; uint8_t v___y_3133_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; uint8_t v___x_3217_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_a_3120_, v_a_3090_);
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref(v___x_3121_);
v___x_3217_ = l_Lean_Expr_hasSorry(v_a_3122_);
if (v___x_3217_ == 0)
{
v___y_3162_ = v_a_3087_;
v___y_3163_ = v_a_3088_;
v___y_3164_ = v_a_3089_;
v___y_3165_ = v_a_3090_;
v___y_3166_ = v___x_3118_;
v___y_3167_ = v_a_3092_;
goto v___jp_3161_;
}
else
{
uint8_t v___x_3218_; 
v___x_3218_ = l_Lean_Expr_hasSyntheticSorry(v_a_3122_);
if (v___x_3218_ == 0)
{
v___y_3199_ = v_a_3087_;
v___y_3200_ = v_a_3088_;
v___y_3201_ = v_a_3089_;
v___y_3202_ = v_a_3090_;
v___y_3203_ = v___x_3118_;
v___y_3204_ = v_a_3092_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3219_; lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec(v_a_3122_);
lean_dec_ref_known(v___x_3118_, 14);
v___x_3219_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
v___jp_3123_:
{
if (v___y_3133_ == 0)
{
if (lean_obj_tag(v___y_3131_) == 0)
{
lean_dec_ref_known(v___y_3131_, 2);
lean_dec_ref(v___y_3126_);
lean_dec(v_a_3122_);
return v___y_3125_;
}
else
{
lean_object* v_id_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3147_; 
v_id_3134_ = lean_ctor_get(v___y_3131_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___y_3131_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___y_3131_, 1);
lean_dec(v_unused_3148_);
v___x_3136_ = v___y_3131_;
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_id_3134_);
lean_dec(v___y_3131_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3124_, v_id_3134_);
lean_dec(v_id_3134_);
if (v___x_3138_ == 0)
{
lean_del_object(v___x_3136_);
lean_dec_ref(v___y_3126_);
lean_dec(v_a_3122_);
return v___y_3125_;
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3143_; 
lean_dec_ref(v___y_3125_);
v___x_3139_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4);
v___x_3140_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6);
v___x_3141_ = l_Lean_indentExpr(v_a_3122_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set_tag(v___x_3136_, 7);
lean_ctor_set(v___x_3136_, 1, v___x_3141_);
lean_ctor_set(v___x_3136_, 0, v___x_3140_);
v___x_3143_ = v___x_3136_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3139_);
v___x_3145_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3144_, v___y_3129_, v___y_3128_, v___y_3130_, v___y_3132_, v___y_3126_, v___y_3127_);
lean_dec_ref(v___y_3126_);
return v___x_3145_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3126_);
lean_dec(v_a_3122_);
return v___y_3125_;
}
}
v___jp_3149_:
{
lean_object* v___x_3156_; 
lean_inc(v_a_3122_);
v___x_3156_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_3122_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_dec_ref(v___y_3154_);
lean_dec(v_a_3122_);
return v___x_3156_;
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
v___x_3158_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3159_ = l_Lean_Exception_isInterrupt(v_a_3157_);
if (v___x_3159_ == 0)
{
uint8_t v___x_3160_; 
lean_inc(v_a_3157_);
v___x_3160_ = l_Lean_Exception_isRuntime(v_a_3157_);
v___y_3124_ = v___x_3158_;
v___y_3125_ = v___x_3156_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3150_;
v___y_3130_ = v___y_3152_;
v___y_3131_ = v_a_3157_;
v___y_3132_ = v___y_3153_;
v___y_3133_ = v___x_3160_;
goto v___jp_3123_;
}
else
{
v___y_3124_ = v___x_3158_;
v___y_3125_ = v___x_3156_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3150_;
v___y_3130_ = v___y_3152_;
v___y_3131_ = v_a_3157_;
v___y_3132_ = v___y_3153_;
v___y_3133_ = v___x_3159_;
goto v___jp_3123_;
}
}
}
v___jp_3161_:
{
lean_object* v___x_3168_; 
lean_inc(v_a_3122_);
v___x_3168_ = l_Lean_Meta_getMVars(v_a_3122_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v___x_3170_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3169_, v___x_3096_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v_a_3169_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; uint8_t v___x_3172_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v___x_3172_ = lean_unbox(v_a_3171_);
lean_dec(v_a_3171_);
if (v___x_3172_ == 0)
{
v___y_3150_ = v___y_3162_;
v___y_3151_ = v___y_3163_;
v___y_3152_ = v___y_3164_;
v___y_3153_ = v___y_3165_;
v___y_3154_ = v___y_3166_;
v___y_3155_ = v___y_3167_;
goto v___jp_3149_;
}
else
{
lean_object* v___x_3173_; lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v___y_3166_);
lean_dec(v_a_3122_);
v___x_3173_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v___y_3166_);
lean_dec(v_a_3122_);
v_a_3182_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3170_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3170_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v___y_3166_);
lean_dec(v_a_3122_);
v_a_3190_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3168_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3168_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
v___jp_3198_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
v___x_3205_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8);
v___x_3206_ = l_Lean_indentExpr(v_a_3122_);
v___x_3207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3207_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec_ref(v___y_3203_);
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref_known(v___x_3118_, 14);
v_a_3228_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3119_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3119_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_stx_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(lean_object* v_config_3276_, lean_object* v_item_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_item_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3296_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3277_, v___x_3295_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3296_) == 0)
{
uint8_t v___x_3297_; 
lean_dec_ref_known(v___x_3296_, 1);
v___x_3297_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3277_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3298_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3277_);
lean_inc_ref(v_item_3277_);
v___x_3299_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3277_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_3301_ = lean_string_dec_eq(v___x_3298_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_3303_ = lean_string_dec_eq(v___x_3298_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_3305_ = lean_string_dec_eq(v___x_3298_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_3307_ = lean_string_dec_eq(v___x_3298_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_3309_ = lean_string_dec_eq(v___x_3298_, v___x_3308_);
lean_dec_ref(v___x_3298_);
if (v___x_3309_ == 0)
{
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_item_3286_ = v___x_3299_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_3311_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3277_, v___x_3310_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3311_) == 0)
{
uint8_t v___x_3312_; 
lean_dec_ref_known(v___x_3311_, 1);
v___x_3312_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3299_);
if (v___x_3312_ == 0)
{
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_item_3286_ = v___x_3299_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v___x_3313_; 
lean_dec_ref(v___x_3299_);
v___x_3313_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3332_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3332_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3332_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
uint8_t v_kernel_3318_; uint8_t v_native_3319_; uint8_t v_revert_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3331_; 
v_kernel_3318_ = lean_ctor_get_uint8(v_config_3276_, 0);
v_native_3319_ = lean_ctor_get_uint8(v_config_3276_, 1);
v_revert_3320_ = lean_ctor_get_uint8(v_config_3276_, 3);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_config_3276_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3322_ = v_config_3276_;
v_isShared_3323_ = v_isSharedCheck_3331_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v_config_3276_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3331_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, 0, v_kernel_3318_);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, 1, v_native_3319_);
v___x_3325_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
uint8_t v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_unbox(v_a_3314_);
lean_dec(v_a_3314_);
lean_ctor_set_uint8(v___x_3325_, 2, v___x_3326_);
lean_ctor_set_uint8(v___x_3325_, 3, v_revert_3320_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3325_);
v___x_3328_ = v___x_3316_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3325_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v_config_3276_);
v_a_3333_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3313_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3313_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_a_3341_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3311_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3311_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec_ref(v___x_3298_);
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_3350_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3277_, v___x_3349_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3350_) == 0)
{
uint8_t v___x_3351_; 
lean_dec_ref_known(v___x_3350_, 1);
v___x_3351_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3299_);
if (v___x_3351_ == 0)
{
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_item_3286_ = v___x_3299_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v___x_3352_; 
lean_dec_ref(v___x_3299_);
v___x_3352_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3371_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3371_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3371_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
uint8_t v_kernel_3357_; uint8_t v_native_3358_; uint8_t v_zetaReduce_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3370_; 
v_kernel_3357_ = lean_ctor_get_uint8(v_config_3276_, 0);
v_native_3358_ = lean_ctor_get_uint8(v_config_3276_, 1);
v_zetaReduce_3359_ = lean_ctor_get_uint8(v_config_3276_, 2);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_config_3276_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3361_ = v_config_3276_;
v_isShared_3362_ = v_isSharedCheck_3370_;
goto v_resetjp_3360_;
}
else
{
lean_dec(v_config_3276_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3370_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3369_, 0, v_kernel_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3369_, 1, v_native_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3369_, 2, v_zetaReduce_3359_);
v___x_3364_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
uint8_t v___x_3365_; lean_object* v___x_3367_; 
v___x_3365_ = lean_unbox(v_a_3353_);
lean_dec(v_a_3353_);
lean_ctor_set_uint8(v___x_3364_, 3, v___x_3365_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3364_);
v___x_3367_ = v___x_3355_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3364_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec_ref(v_config_3276_);
v_a_3372_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3352_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3352_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_a_3380_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3350_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3350_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec_ref(v___x_3298_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_3389_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3277_, v___x_3388_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3389_) == 0)
{
uint8_t v___x_3390_; 
lean_dec_ref_known(v___x_3389_, 1);
v___x_3390_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3299_);
if (v___x_3390_ == 0)
{
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_item_3286_ = v___x_3299_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v___x_3391_; 
lean_dec_ref(v___x_3299_);
v___x_3391_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3410_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3410_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3410_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
uint8_t v_kernel_3396_; uint8_t v_zetaReduce_3397_; uint8_t v_revert_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3409_; 
v_kernel_3396_ = lean_ctor_get_uint8(v_config_3276_, 0);
v_zetaReduce_3397_ = lean_ctor_get_uint8(v_config_3276_, 2);
v_revert_3398_ = lean_ctor_get_uint8(v_config_3276_, 3);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_config_3276_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3400_ = v_config_3276_;
v_isShared_3401_ = v_isSharedCheck_3409_;
goto v_resetjp_3399_;
}
else
{
lean_dec(v_config_3276_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3409_;
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
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 0, v_kernel_3396_);
v___x_3403_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
uint8_t v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_unbox(v_a_3392_);
lean_dec(v_a_3392_);
lean_ctor_set_uint8(v___x_3403_, 1, v___x_3404_);
lean_ctor_set_uint8(v___x_3403_, 2, v_zetaReduce_3397_);
lean_ctor_set_uint8(v___x_3403_, 3, v_revert_3398_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v___x_3403_);
v___x_3406_ = v___x_3394_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3403_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_config_3276_);
v_a_3411_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3391_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3391_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_a_3419_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3389_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3389_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec_ref(v___x_3298_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_3428_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3277_, v___x_3427_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3428_) == 0)
{
uint8_t v___x_3429_; 
lean_dec_ref_known(v___x_3428_, 1);
v___x_3429_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3299_);
if (v___x_3429_ == 0)
{
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_item_3286_ = v___x_3299_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v___x_3430_; 
lean_dec_ref(v___x_3299_);
v___x_3430_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3449_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3449_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3449_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
uint8_t v_native_3435_; uint8_t v_zetaReduce_3436_; uint8_t v_revert_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3448_; 
v_native_3435_ = lean_ctor_get_uint8(v_config_3276_, 1);
v_zetaReduce_3436_ = lean_ctor_get_uint8(v_config_3276_, 2);
v_revert_3437_ = lean_ctor_get_uint8(v_config_3276_, 3);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_config_3276_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3439_ = v_config_3276_;
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
else
{
lean_dec(v_config_3276_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 0, 4);
v___x_3442_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
uint8_t v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_unbox(v_a_3431_);
lean_dec(v_a_3431_);
lean_ctor_set_uint8(v___x_3442_, 0, v___x_3443_);
lean_ctor_set_uint8(v___x_3442_, 1, v_native_3435_);
lean_ctor_set_uint8(v___x_3442_, 2, v_zetaReduce_3436_);
lean_ctor_set_uint8(v___x_3442_, 3, v_revert_3437_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3442_);
v___x_3445_ = v___x_3433_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3442_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec_ref(v_config_3276_);
v_a_3450_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3430_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3430_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_a_3458_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3428_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3428_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
else
{
uint8_t v___x_3466_; 
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_config_3276_);
v___x_3466_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3299_);
if (v___x_3466_ == 0)
{
lean_dec_ref(v_item_3277_);
v_item_3286_ = v___x_3299_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v_value_3467_; lean_object* v___x_3468_; 
lean_dec_ref(v___x_3299_);
v_value_3467_ = lean_ctor_get(v_item_3277_, 2);
lean_inc(v_value_3467_);
lean_dec_ref(v_item_3277_);
v___x_3468_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_value_3467_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3468_;
}
}
}
else
{
lean_dec_ref(v_config_3276_);
v_item_3286_ = v_item_3277_;
v___y_3287_ = v___y_3278_;
v___y_3288_ = v___y_3279_;
v___y_3289_ = v___y_3280_;
v___y_3290_ = v___y_3281_;
v___y_3291_ = v___y_3282_;
v___y_3292_ = v___y_3283_;
goto v___jp_3285_;
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v_item_3277_);
lean_dec_ref(v_config_3276_);
v_a_3469_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3296_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3296_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
v___jp_3285_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_3294_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3286_, v___x_3293_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3477_, lean_object* v_item_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(v_config_3477_, v_item_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_00_u03b1_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(v_00_u03b1_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
return v_res_3506_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = lean_box(0);
v___x_3508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3509_ = l_Lean_mkConst(v___x_3508_, v___x_3507_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0);
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(lean_object* v_cfg_3512_, lean_object* v_cfgItem_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1);
v___x_3522_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3512_, v_cfgItem_3513_, v___x_3521_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_3523_, lean_object* v_cfgItem_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(v_cfg_3523_, v_cfgItem_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_cfgItem_3524_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object* v_cfg_3534_, lean_object* v_init_3535_, uint8_t v_logExceptions_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_onErr_3541_; lean_object* v_eval_3542_; 
v_onErr_3541_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0));
v_eval_3542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_3536_ == 0)
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3542_, v_init_3535_, v_cfg_3534_, v_onErr_3541_, v_logExceptions_3536_, v_a_3538_, v_a_3539_);
return v___x_3543_;
}
else
{
uint8_t v_recover_3544_; lean_object* v___x_3545_; 
v_recover_3544_ = lean_ctor_get_uint8(v_a_3537_, sizeof(void*)*1);
v___x_3545_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3542_, v_init_3535_, v_cfg_3534_, v_onErr_3541_, v_recover_3544_, v_a_3538_, v_a_3539_);
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object* v_cfg_3546_, lean_object* v_init_3547_, lean_object* v_logExceptions_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
uint8_t v_logExceptions_boxed_3553_; lean_object* v_res_3554_; 
v_logExceptions_boxed_3553_ = lean_unbox(v_logExceptions_3548_);
v_res_3554_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_cfg_3546_, v_init_3547_, v_logExceptions_boxed_3553_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* v_cfg_3555_, lean_object* v_init_3556_, uint8_t v_logExceptions_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_cfg_3555_, v_init_3556_, v_logExceptions_3557_, v_a_3558_, v_a_3564_, v_a_3565_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* v_cfg_3568_, lean_object* v_init_3569_, lean_object* v_logExceptions_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
uint8_t v_logExceptions_boxed_3580_; lean_object* v_res_3581_; 
v_logExceptions_boxed_3580_ = lean_unbox(v_logExceptions_3570_);
v_res_3581_ = l_Lean_Elab_Tactic_elabDecideConfig(v_cfg_3568_, v_init_3569_, v_logExceptions_boxed_3580_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* v_stx_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = l_Lean_Syntax_getArg(v_stx_3587_, v___x_3597_);
v___x_3599_ = 1;
v___x_3600_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__0));
v___x_3601_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3598_, v___x_3600_, v___x_3599_, v_a_3588_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
v___x_3603_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__1));
v___x_3604_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3603_, v_a_3602_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_a_3602_);
return v___x_3604_;
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
v_a_3605_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3601_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3601_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object* v_stx_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Elab_Tactic_evalDecide(v_stx_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_stx_3613_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3637_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0));
v___x_3639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
v___x_3641_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3637_, v___x_3638_, v___x_3639_, v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object* v_a_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6));
v___x_3672_ = l_Lean_addBuiltinDeclarationRanges(v___x_3670_, v___x_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* v_stx_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = l_Lean_Syntax_getArg(v_stx_3678_, v___x_3688_);
v___x_3690_ = 1;
v___x_3691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__0));
v___x_3692_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3689_, v___x_3691_, v___x_3690_, v_a_3679_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; uint8_t v_kernel_3694_; uint8_t v_zetaReduce_3695_; uint8_t v_revert_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3705_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v_kernel_3694_ = lean_ctor_get_uint8(v_a_3693_, 0);
v_zetaReduce_3695_ = lean_ctor_get_uint8(v_a_3693_, 2);
v_revert_3696_ = lean_ctor_get_uint8(v_a_3693_, 3);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_a_3693_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3698_ = v_a_3693_;
v_isShared_3699_ = v_isSharedCheck_3705_;
goto v_resetjp_3697_;
}
else
{
lean_dec(v_a_3693_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3705_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 0, v_kernel_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 2, v_zetaReduce_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3704_, 3, v_revert_3696_);
v___x_3701_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_ctor_set_uint8(v___x_3701_, 1, v___x_3690_);
v___x_3702_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___closed__1));
v___x_3703_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3702_, v___x_3701_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
lean_dec_ref(v___x_3701_);
return v___x_3703_;
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
v_a_3706_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3692_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3692_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object* v_stx_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Elab_Tactic_evalNativeDecide(v_stx_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_stx_3714_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3738_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1));
v___x_3740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3741_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
v___x_3742_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3738_, v___x_3739_, v___x_3740_, v___x_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6));
v___x_3773_ = l_Lean_addBuiltinDeclarationRanges(v___x_3771_, v___x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
return v_res_3775_;
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
