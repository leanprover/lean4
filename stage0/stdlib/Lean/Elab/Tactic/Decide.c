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
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
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
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 237, 71, 156, 244, 3, 80, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 96, 18, 10, 225, 62, 78, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4_value)}};
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_104_; lean_object* v_options_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_toCold_104_ = lean_ctor_get(v___y_102_, 0);
v_options_105_ = lean_ctor_get(v_toCold_104_, 2);
v___x_106_ = l_Lean_Elab_pp_macroStack;
v___x_107_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v_options_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec(v_macroStack_101_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v_msgData_100_);
return v___x_108_;
}
else
{
if (lean_obj_tag(v_macroStack_101_) == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v_msgData_100_);
return v___x_109_;
}
else
{
lean_object* v_head_110_; lean_object* v_after_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_126_; 
v_head_110_ = lean_ctor_get(v_macroStack_101_, 0);
lean_inc(v_head_110_);
v_after_111_ = lean_ctor_get(v_head_110_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_head_110_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v_head_110_, 0);
lean_dec(v_unused_127_);
v___x_113_ = v_head_110_;
v_isShared_114_ = v_isSharedCheck_126_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_after_111_);
lean_dec(v_head_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_126_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 7);
lean_ctor_set(v___x_113_, 1, v___x_115_);
lean_ctor_set(v___x_113_, 0, v_msgData_100_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_msgData_100_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_125_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_msgData_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_118_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2);
v___x_119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = l_Lean_MessageData_ofSyntax(v_after_111_);
v___x_121_ = l_Lean_indentD(v___x_120_);
v_msgData_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_122_, 0, v___x_119_);
lean_ctor_set(v_msgData_122_, 1, v___x_121_);
v___x_123_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4(v_msgData_122_, v_macroStack_101_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_128_, lean_object* v_macroStack_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_128_, v_macroStack_129_, v___y_130_);
lean_dec_ref(v___y_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(lean_object* v_msgData_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; lean_object* v_env_140_; lean_object* v___x_141_; lean_object* v_toCold_142_; lean_object* v_mctx_143_; lean_object* v_lctx_144_; lean_object* v_options_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_139_ = lean_st_ref_get(v___y_137_);
v_env_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_env_140_);
lean_dec(v___x_139_);
v___x_141_ = lean_st_ref_get(v___y_135_);
v_toCold_142_ = lean_ctor_get(v___y_136_, 0);
v_mctx_143_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref(v_mctx_143_);
lean_dec(v___x_141_);
v_lctx_144_ = lean_ctor_get(v___y_134_, 2);
v_options_145_ = lean_ctor_get(v_toCold_142_, 2);
lean_inc_ref(v_options_145_);
lean_inc_ref(v_lctx_144_);
v___x_146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_146_, 0, v_env_140_);
lean_ctor_set(v___x_146_, 1, v_mctx_143_);
lean_ctor_set(v___x_146_, 2, v_lctx_144_);
lean_ctor_set(v___x_146_, 3, v_options_145_);
v___x_147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_msgData_133_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0___boxed(lean_object* v_msgData_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msgData_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_ref_164_; lean_object* v___x_165_; lean_object* v_a_166_; lean_object* v_macroStack_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
v_ref_164_ = lean_ctor_get(v___y_161_, 2);
v___x_165_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_156_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref(v___x_165_);
v_macroStack_167_ = lean_ctor_get(v___y_157_, 1);
v___x_168_ = l_Lean_Elab_getBetterRef(v_ref_164_, v_macroStack_167_);
lean_inc(v_macroStack_167_);
v___x_169_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_a_166_, v_macroStack_167_, v___y_161_);
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_178_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_168_);
lean_ctor_set(v___x_174_, 1, v_a_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 1);
lean_ctor_set(v___x_172_, 0, v___x_174_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg___boxed(lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_187_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0));
v___x_190_ = l_Lean_stringToMessageData(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3);
v___x_195_ = l_Lean_MessageData_hint_x27(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object* v_expectedType_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v_expectedType_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___x_252_; lean_object* v_a_253_; uint8_t v___x_254_; 
v___x_252_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_expectedType_199_, v_a_203_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_254_ = l_Lean_Expr_hasFVar(v_a_253_);
if (v___x_254_ == 0)
{
v_expectedType_232_ = v_a_253_;
v___y_233_ = v_a_200_;
v___y_234_ = v_a_201_;
v___y_235_ = v_a_202_;
v___y_236_ = v_a_203_;
v___y_237_ = v_a_204_;
v___y_238_ = v_a_205_;
goto v___jp_231_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Meta_zetaReduce(v_a_253_, v___x_254_, v___x_254_, v___x_254_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
v_expectedType_232_ = v_a_256_;
v___y_233_ = v_a_200_;
v___y_234_ = v_a_201_;
v___y_235_ = v_a_202_;
v___y_236_ = v_a_203_;
v___y_237_ = v_a_204_;
v___y_238_ = v_a_205_;
goto v___jp_231_;
}
else
{
return v___x_255_;
}
}
v___jp_207_:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_Expr_hasFVar(v___y_208_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___y_208_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v___x_217_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1);
v___x_218_ = l_Lean_indentExpr(v___y_208_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_221_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
v___jp_231_:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_Expr_hasMVar(v_expectedType_232_);
if (v___x_239_ == 0)
{
v___y_208_ = v_expectedType_232_;
v___y_209_ = v___y_233_;
v___y_210_ = v___y_234_;
v___y_211_ = v___y_235_;
v___y_212_ = v___y_236_;
v___y_213_ = v___y_237_;
v___y_214_ = v___y_238_;
goto v___jp_207_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v___x_240_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6);
v___x_241_ = l_Lean_indentExpr(v_expectedType_232_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_242_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(lean_object* v_expectedType_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(lean_object* v_00_u03b1_266_, lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___boxed(lean_object* v_00_u03b1_276_, lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(v_00_u03b1_276_, v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(lean_object* v_msgData_286_, lean_object* v_macroStack_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_286_, v_macroStack_287_, v___y_292_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___boxed(lean_object* v_msgData_296_, lean_object* v_macroStack_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(v_msgData_296_, v_macroStack_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(lean_object* v_declName_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_env_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
v___x_311_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_310_, v_declName_306_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(lean_object* v_declName_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_313_, v___y_314_);
lean_dec(v___y_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(lean_object* v_declName_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_317_, v___y_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(lean_object* v_declName_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(v_declName_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = l_Lean_maxRecDepthErrorMessage;
v___x_337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3);
v___x_339_ = l_Lean_MessageData_ofFormat(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4);
v___x_341_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_342_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object* v_ref_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_ref_343_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object* v_ref_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object* v_00_u03b1_351_, lean_object* v_ref_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_352_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object* v_00_u03b1_359_, lean_object* v_ref_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(v_00_u03b1_359_, v_ref_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_366_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0(void){
_start:
{
lean_object* v___x_384_; lean_object* v_dummy_385_; 
v___x_384_ = lean_box(0);
v_dummy_385_ = l_Lean_Expr_sort___override(v___x_384_);
return v_dummy_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* v_expr_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v_toCold_499_; lean_object* v_currRecDepth_500_; lean_object* v_ref_501_; uint8_t v_diag_502_; uint8_t v_suppressElabErrors_503_; lean_object* v_maxRecDepth_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_toCold_499_ = lean_ctor_get(v_a_400_, 0);
lean_inc_ref(v_toCold_499_);
v_currRecDepth_500_ = lean_ctor_get(v_a_400_, 1);
lean_inc(v_currRecDepth_500_);
v_ref_501_ = lean_ctor_get(v_a_400_, 2);
lean_inc(v_ref_501_);
v_diag_502_ = lean_ctor_get_uint8(v_a_400_, sizeof(void*)*3);
v_suppressElabErrors_503_ = lean_ctor_get_uint8(v_a_400_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_400_);
v_maxRecDepth_517_ = lean_ctor_get(v_toCold_499_, 3);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_eq(v_maxRecDepth_517_, v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_eq(v_currRecDepth_500_, v_maxRecDepth_517_);
if (v___x_520_ == 0)
{
goto v___jp_504_;
}
else
{
lean_object* v___x_521_; 
lean_dec(v_currRecDepth_500_);
lean_dec_ref(v_toCold_499_);
lean_dec_ref(v_expr_397_);
v___x_521_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_ref_501_);
return v___x_521_;
}
}
else
{
goto v___jp_504_;
}
v___jp_403_:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Expr_getAppFn(v___y_405_);
if (lean_obj_tag(v___x_411_) == 4)
{
lean_object* v_declName_412_; lean_object* v___x_413_; 
v_declName_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_declName_412_);
lean_dec_ref_known(v___x_411_, 2);
v___x_413_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_412_, v___y_410_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_456_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_456_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_456_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_456_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
if (lean_obj_tag(v_a_414_) == 1)
{
lean_object* v_val_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_val_418_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_a_414_, 1);
v___x_419_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_418_);
v___x_420_ = lean_nat_dec_le(v___x_419_, v___y_404_);
lean_dec(v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_val_418_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_404_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___y_405_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___y_405_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_object* v_numDiscrs_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_dummy_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_del_object(v___x_416_);
v_numDiscrs_424_ = lean_ctor_get(v_val_418_, 1);
lean_inc(v_numDiscrs_424_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1));
v_dummy_427_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0);
lean_inc(v___y_404_);
v___x_428_ = lean_mk_array(v___y_404_, v_dummy_427_);
v___x_429_ = lean_nat_sub(v___y_404_, v___y_406_);
lean_dec(v___y_404_);
lean_inc_ref(v___y_405_);
v___x_430_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_405_, v___x_428_, v___x_429_);
v___x_431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_numDiscrs_424_, v_val_418_, v___x_430_, v___x_425_, v___x_426_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec_ref(v___x_430_);
lean_dec(v_val_418_);
lean_dec(v_numDiscrs_424_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_444_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_444_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_fst_436_; 
v_fst_436_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_fst_436_);
lean_dec(v_a_432_);
if (lean_obj_tag(v_fst_436_) == 0)
{
lean_object* v___x_438_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___y_405_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___y_405_);
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
lean_object* v_val_440_; lean_object* v___x_442_; 
lean_dec_ref(v___y_405_);
v_val_440_ = lean_ctor_get(v_fst_436_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_fst_436_, 1);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_val_440_);
v___x_442_ = v___x_434_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_val_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___y_405_);
v_a_445_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_431_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_431_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
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
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v_a_414_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_404_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___y_405_);
v___x_454_ = v___x_416_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___y_405_);
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
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v___y_409_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
v_a_457_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_413_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_413_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v___x_465_; 
lean_dec_ref(v___x_411_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_404_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___y_405_);
return v___x_465_;
}
}
v___jp_466_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3));
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2));
v___x_473_ = lean_unsigned_to_nat(3u);
v___x_474_ = l_Lean_Expr_isAppOfArity(v___y_469_, v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
if (lean_obj_tag(v___y_469_) == 11)
{
lean_object* v_typeName_475_; 
v_typeName_475_ = lean_ctor_get(v___y_469_, 0);
if (lean_obj_tag(v_typeName_475_) == 1)
{
lean_object* v_pre_476_; 
v_pre_476_ = lean_ctor_get(v_typeName_475_, 0);
if (lean_obj_tag(v_pre_476_) == 0)
{
lean_object* v_idx_477_; lean_object* v_struct_478_; lean_object* v_str_479_; uint8_t v___x_480_; 
v_idx_477_ = lean_ctor_get(v___y_469_, 1);
v_struct_478_ = lean_ctor_get(v___y_469_, 2);
v_str_479_ = lean_ctor_get(v_typeName_475_, 1);
v___x_480_ = lean_string_dec_eq(v_str_479_, v___x_471_);
if (v___x_480_ == 0)
{
v___y_404_ = v___y_467_;
v___y_405_ = v___y_469_;
v___y_406_ = v___y_470_;
v___y_407_ = v_a_398_;
v___y_408_ = v_a_399_;
v___y_409_ = v___y_468_;
v___y_410_ = v_a_401_;
goto v___jp_403_;
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_nat_dec_eq(v_idx_477_, v___x_481_);
if (v___x_482_ == 0)
{
v___y_404_ = v___y_467_;
v___y_405_ = v___y_469_;
v___y_406_ = v___y_470_;
v___y_407_ = v_a_398_;
v___y_408_ = v_a_399_;
v___y_409_ = v___y_468_;
v___y_410_ = v_a_401_;
goto v___jp_403_;
}
else
{
lean_inc_ref(v_struct_478_);
lean_dec_ref_known(v___y_469_, 3);
lean_dec(v___y_467_);
v_expr_397_ = v_struct_478_;
v_a_400_ = v___y_468_;
goto _start;
}
}
}
else
{
v___y_404_ = v___y_467_;
v___y_405_ = v___y_469_;
v___y_406_ = v___y_470_;
v___y_407_ = v_a_398_;
v___y_408_ = v_a_399_;
v___y_409_ = v___y_468_;
v___y_410_ = v_a_401_;
goto v___jp_403_;
}
}
else
{
v___y_404_ = v___y_467_;
v___y_405_ = v___y_469_;
v___y_406_ = v___y_470_;
v___y_407_ = v_a_398_;
v___y_408_ = v_a_399_;
v___y_409_ = v___y_468_;
v___y_410_ = v_a_401_;
goto v___jp_403_;
}
}
else
{
v___y_404_ = v___y_467_;
v___y_405_ = v___y_469_;
v___y_406_ = v___y_470_;
v___y_407_ = v_a_398_;
v___y_408_ = v_a_399_;
v___y_409_ = v___y_468_;
v___y_410_ = v_a_401_;
goto v___jp_403_;
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v___y_467_);
v___x_484_ = l_Lean_Expr_appFn_x21(v___y_469_);
lean_dec_ref(v___y_469_);
v___x_485_ = l_Lean_Expr_appArg_x21(v___x_484_);
lean_dec_ref(v___x_484_);
v_expr_397_ = v___x_485_;
v_a_400_ = v___y_468_;
goto _start;
}
}
v___jp_487_:
{
if (v___y_488_ == 0)
{
v___y_467_ = v___y_489_;
v___y_468_ = v___y_490_;
v___y_469_ = v___y_491_;
v___y_470_ = v___y_492_;
goto v___jp_466_;
}
else
{
if (v___y_493_ == 0)
{
v___y_467_ = v___y_489_;
v___y_468_ = v___y_490_;
v___y_469_ = v___y_491_;
v___y_470_ = v___y_492_;
goto v___jp_466_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(3u);
v___x_495_ = lean_nat_sub(v___y_489_, v___x_494_);
lean_dec(v___y_489_);
v___x_496_ = lean_nat_sub(v___x_495_, v___y_492_);
lean_dec(v___x_495_);
v___x_497_ = l_Lean_Expr_getRevArg_x21(v___y_491_, v___x_496_);
lean_dec_ref(v___y_491_);
v_expr_397_ = v___x_497_;
v_a_400_ = v___y_490_;
goto _start;
}
}
}
v___jp_504_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_currRecDepth_500_, v___x_505_);
lean_dec(v_currRecDepth_500_);
v___x_507_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_507_, 0, v_toCold_499_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v_ref_501_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3, v_diag_502_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3 + 1, v_suppressElabErrors_503_);
lean_inc(v_a_401_);
lean_inc_ref(v___x_507_);
lean_inc(v_a_399_);
lean_inc_ref(v_a_398_);
v___x_508_ = lean_whnf(v_expr_397_, v_a_398_, v_a_399_, v___x_507_, v_a_401_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = l_Lean_Expr_getAppNumArgs(v_a_509_);
v___x_511_ = lean_unsigned_to_nat(4u);
v___x_512_ = lean_nat_dec_le(v___x_511_, v___x_510_);
v___x_513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4));
v___x_514_ = l_Lean_Expr_isAppOf(v_a_509_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__5));
v___x_516_ = l_Lean_Expr_isAppOf(v_a_509_, v___x_515_);
v___y_488_ = v___x_512_;
v___y_489_ = v___x_510_;
v___y_490_ = v___x_507_;
v___y_491_ = v_a_509_;
v___y_492_ = v___x_505_;
v___y_493_ = v___x_516_;
goto v___jp_487_;
}
else
{
v___y_488_ = v___x_512_;
v___y_489_ = v___x_510_;
v___y_490_ = v___x_507_;
v___y_491_ = v_a_509_;
v___y_492_ = v___x_505_;
v___y_493_ = v___x_514_;
goto v___jp_487_;
}
}
else
{
lean_dec_ref_known(v___x_507_, 3);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(lean_object* v_upperBound_522_, lean_object* v_val_523_, lean_object* v___x_524_, lean_object* v_a_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_a_533_; uint8_t v___x_537_; 
v___x_537_ = lean_nat_dec_lt(v_a_525_, v_upperBound_522_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec(v_a_525_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_b_526_);
return v___x_538_;
}
else
{
lean_object* v_numParams_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v_b_526_);
v_numParams_539_ = lean_ctor_get(v_val_523_, 0);
v___x_540_ = l_Lean_instInhabitedExpr;
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_numParams_539_, v___x_541_);
v___x_543_ = lean_nat_add(v___x_542_, v_a_525_);
lean_dec(v___x_542_);
v___x_544_ = lean_array_get_borrowed(v___x_540_, v___x_524_, v___x_543_);
lean_dec(v___x_543_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
lean_inc(v___x_544_);
v___x_545_ = lean_infer_type(v___x_544_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
v___x_547_ = lean_whnf(v_a_546_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = lean_box(0);
v___x_550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__1));
v___x_551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2));
v___x_552_ = l_Lean_Expr_isConstOf(v_a_548_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4));
v___x_554_ = l_Lean_Expr_isAppOf(v_a_548_, v___x_553_);
lean_dec(v_a_548_);
if (v___x_554_ == 0)
{
v_a_533_ = v___x_550_;
goto v___jp_532_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_544_);
v___x_556_ = l_Lean_Expr_proj___override(v___x_553_, v___x_555_, v___x_544_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
v___x_557_ = lean_whnf(v___x_556_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; uint8_t v___y_560_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_580_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_581_ = l_Lean_Expr_isConstOf(v_a_558_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_583_ = l_Lean_Expr_isConstOf(v_a_558_, v___x_582_);
v___y_560_ = v___x_583_;
goto v___jp_559_;
}
else
{
v___y_560_ = v___x_581_;
goto v___jp_559_;
}
v___jp_559_:
{
if (v___y_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec(v_a_525_);
lean_inc_ref(v___y_529_);
v___x_561_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_558_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_571_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_a_562_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_549_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_a_572_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_561_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_561_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_dec(v_a_558_);
v_a_533_ = v___x_550_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_525_);
v_a_584_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_557_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_557_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec(v_a_548_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
lean_inc(v___x_544_);
v___x_592_ = lean_whnf(v___x_544_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; uint8_t v___y_595_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_615_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_616_ = l_Lean_Expr_isConstOf(v_a_593_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_618_ = l_Lean_Expr_isConstOf(v_a_593_, v___x_617_);
v___y_595_ = v___x_618_;
goto v___jp_594_;
}
else
{
v___y_595_ = v___x_616_;
goto v___jp_594_;
}
v___jp_594_:
{
if (v___y_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v_a_525_);
lean_inc_ref(v___y_529_);
v___x_596_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_593_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
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
lean_ctor_set(v___x_602_, 1, v___x_549_);
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
lean_dec(v_a_593_);
v_a_533_ = v___x_550_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_a_525_);
v_a_619_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_592_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_592_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_525_);
v_a_627_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_547_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_547_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_525_);
v_a_635_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_545_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_545_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_a_525_, v___x_534_);
lean_dec(v_a_525_);
lean_inc_ref(v_a_533_);
v_a_525_ = v___x_535_;
v_b_526_ = v_a_533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___boxed(lean_object* v_upperBound_643_, lean_object* v_val_644_, lean_object* v___x_645_, lean_object* v_a_646_, lean_object* v_b_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_upperBound_643_, v_val_644_, v___x_645_, v_a_646_, v_b_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___x_645_);
lean_dec_ref(v_val_644_);
lean_dec(v_upperBound_643_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object* v_expr_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_expr_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(lean_object* v_upperBound_661_, lean_object* v_val_662_, lean_object* v___x_663_, lean_object* v_inst_664_, lean_object* v_R_665_, lean_object* v_a_666_, lean_object* v_b_667_, lean_object* v_c_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg(v_upperBound_661_, v_val_662_, v___x_663_, v_a_666_, v_b_667_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(lean_object* v_upperBound_675_, lean_object* v_val_676_, lean_object* v___x_677_, lean_object* v_inst_678_, lean_object* v_R_679_, lean_object* v_a_680_, lean_object* v_b_681_, lean_object* v_c_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_upperBound_675_, v_val_676_, v___x_677_, v_inst_678_, v_R_679_, v_a_680_, v_b_681_, v_c_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v_val_676_);
lean_dec(v_upperBound_675_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(lean_object* v_msg_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_ref_695_; lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
v_ref_695_ = lean_ctor_get(v___y_692_, 2);
v___x_696_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc(v_ref_695_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_ref_695_);
lean_ctor_set(v___x_701_, 1, v_a_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 1);
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_712_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_box(0);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1));
v___x_718_ = l_Lean_mkConst(v___x_717_, v___x_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3));
v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore(lean_object* v_tacticName_728_, lean_object* v_expectedType_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
lean_inc_ref(v_expectedType_729_);
v___x_739_ = l_Lean_Meta_mkDecide(v_expectedType_729_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_779_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_779_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_779_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_779_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_ref_744_; lean_object* v___x_746_; 
v_ref_744_ = lean_ctor_get(v_a_736_, 2);
lean_inc(v_ref_744_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 0, v_ref_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_ref_744_);
v___x_746_ = v_reuseFailAlloc_778_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
lean_inc(v_a_740_);
lean_inc(v_tacticName_728_);
v___x_747_ = l_Lean_Meta_nativeEqTrue(v_tacticName_728_, v_a_740_, v___x_746_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec_ref(v___x_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_769_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_769_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_769_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_769_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
if (lean_obj_tag(v_a_748_) == 0)
{
lean_object* v_prf_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v_tacticName_728_);
v_prf_752_ = lean_ctor_get(v_a_748_, 0);
lean_inc_ref(v_prf_752_);
lean_dec_ref_known(v_a_748_, 1);
v___x_753_ = l_Lean_Expr_appArg_x21(v_a_740_);
lean_dec(v_a_740_);
v___x_754_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_755_ = l_Lean_mkApp3(v___x_754_, v_expectedType_729_, v___x_753_, v_prf_752_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_755_);
v___x_757_ = v___x_750_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_del_object(v___x_750_);
lean_dec(v_a_740_);
v___x_759_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_760_ = l_Lean_MessageData_ofName(v_tacticName_728_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l_Lean_indentExpr(v_expectedType_729_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_767_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_768_;
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_740_);
lean_dec_ref(v_expectedType_729_);
lean_dec(v_tacticName_728_);
v_a_770_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_747_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_747_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
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
}
else
{
lean_dec_ref(v_expectedType_729_);
lean_dec(v_tacticName_728_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(lean_object* v_tacticName_780_, lean_object* v_expectedType_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_780_, v_expectedType_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(lean_object* v_00_u03b1_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_793_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(lean_object* v_00_u03b1_804_, lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(v_00_u03b1_804_, v_msg_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_815_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
if (lean_obj_tag(v_x_817_) == 0)
{
uint8_t v___x_818_; 
v___x_818_ = 1;
return v___x_818_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
}
else
{
if (lean_obj_tag(v_x_817_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
else
{
lean_object* v_val_821_; lean_object* v_val_822_; uint8_t v___x_823_; 
v_val_821_ = lean_ctor_get(v_x_816_, 0);
v_val_822_ = lean_ctor_get(v_x_817_, 0);
v___x_823_ = lean_name_eq(v_val_821_, v_val_822_);
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_x_824_, v_x_825_);
lean_dec(v_x_825_);
lean_dec(v_x_824_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object* v_opts_828_, lean_object* v_opt_829_){
_start:
{
lean_object* v_name_830_; lean_object* v_defValue_831_; lean_object* v_map_832_; lean_object* v___x_833_; 
v_name_830_ = lean_ctor_get(v_opt_829_, 0);
v_defValue_831_ = lean_ctor_get(v_opt_829_, 1);
v_map_832_ = lean_ctor_get(v_opts_828_, 0);
v___x_833_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_832_, v_name_830_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_inc(v_defValue_831_);
return v_defValue_831_;
}
else
{
lean_object* v_val_834_; 
v_val_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v___x_833_, 1);
if (lean_obj_tag(v_val_834_) == 3)
{
lean_object* v_v_835_; 
v_v_835_ = lean_ctor_get(v_val_834_, 0);
lean_inc(v_v_835_);
lean_dec_ref_known(v_val_834_, 1);
return v_v_835_;
}
else
{
lean_dec(v_val_834_);
lean_inc(v_defValue_831_);
return v_defValue_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object* v_opts_836_, lean_object* v_opt_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_opts_836_, v_opt_837_);
lean_dec_ref(v_opt_837_);
lean_dec_ref(v_opts_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_saveState___redArg(v___y_841_, v___y_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_r_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
v_r_847_ = lean_apply_5(v_x_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, lean_box(0));
if (lean_obj_tag(v_r_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_ctor_get(v_r_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v_r_847_, 1);
v___x_849_ = l_Lean_Meta_SavedState_restore___redArg(v_a_846_, v___y_841_, v___y_843_);
lean_dec(v_a_846_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v___x_849_, 0);
lean_dec(v_unused_857_);
v___x_851_ = v___x_849_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_dec(v___x_849_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_a_848_);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_848_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_848_);
v_a_858_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_849_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_849_);
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
else
{
lean_object* v_a_866_; lean_object* v___x_867_; 
v_a_866_ = lean_ctor_get(v_r_847_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v_r_847_, 1);
v___x_867_ = l_Lean_Meta_SavedState_restore___redArg(v_a_846_, v___y_841_, v___y_843_);
lean_dec(v_a_846_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_875_);
v___x_869_ = v___x_867_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_dec(v___x_867_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 1);
lean_ctor_set(v___x_869_, 0, v_a_866_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_866_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_866_);
v_a_876_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_867_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_x_839_);
v_a_884_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_845_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_845_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg___boxed(lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v_x_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(lean_object* v_00_u03b1_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v_x_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___boxed(lean_object* v_00_u03b1_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7(v_00_u03b1_907_, v_x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object* v_cs_915_, lean_object* v_n_916_, lean_object* v_x_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_array_push(v_cs_915_, v_n_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object* v_cs_919_, lean_object* v_n_920_, lean_object* v_x_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(v_cs_919_, v_n_920_, v_x_921_);
lean_dec(v_x_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___lam__0(lean_object* v_f_923_, lean_object* v_x1_924_, lean_object* v_x2_925_, lean_object* v_x3_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_apply_3(v_f_923_, v_x1_924_, v_x2_925_, v_x3_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(lean_object* v_f_928_, lean_object* v_keys_929_, lean_object* v_vals_930_, lean_object* v_i_931_, lean_object* v_acc_932_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_keys_929_);
v___x_934_ = lean_nat_dec_lt(v_i_931_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec(v_i_931_);
lean_dec(v_f_928_);
return v_acc_932_;
}
else
{
lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_k_935_ = lean_array_fget_borrowed(v_keys_929_, v_i_931_);
v_v_936_ = lean_array_fget_borrowed(v_vals_930_, v_i_931_);
lean_inc(v_f_928_);
lean_inc(v_v_936_);
lean_inc(v_k_935_);
v___x_937_ = lean_apply_3(v_f_928_, v_acc_932_, v_k_935_, v_v_936_);
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_add(v_i_931_, v___x_938_);
lean_dec(v_i_931_);
v_i_931_ = v___x_939_;
v_acc_932_ = v___x_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_f_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_i_944_, lean_object* v_acc_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(v_f_941_, v_keys_942_, v_vals_943_, v_i_944_, v_acc_945_);
lean_dec_ref(v_vals_943_);
lean_dec_ref(v_keys_942_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(lean_object* v_f_947_, lean_object* v_as_948_, size_t v_i_949_, size_t v_stop_950_, lean_object* v_b_951_){
_start:
{
lean_object* v___y_953_; uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_eq(v_i_949_, v_stop_950_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_array_uget_borrowed(v_as_948_, v_i_949_);
switch(lean_obj_tag(v___x_958_))
{
case 0:
{
lean_object* v_key_959_; lean_object* v_val_960_; lean_object* v___x_961_; 
v_key_959_ = lean_ctor_get(v___x_958_, 0);
v_val_960_ = lean_ctor_get(v___x_958_, 1);
lean_inc(v_f_947_);
lean_inc(v_val_960_);
lean_inc(v_key_959_);
v___x_961_ = lean_apply_3(v_f_947_, v_b_951_, v_key_959_, v_val_960_);
v___y_953_ = v___x_961_;
goto v___jp_952_;
}
case 1:
{
lean_object* v_node_962_; lean_object* v___x_963_; 
v_node_962_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_f_947_);
v___x_963_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_947_, v_node_962_, v_b_951_);
v___y_953_ = v___x_963_;
goto v___jp_952_;
}
default: 
{
v___y_953_ = v_b_951_;
goto v___jp_952_;
}
}
}
else
{
lean_dec(v_f_947_);
return v_b_951_;
}
v___jp_952_:
{
size_t v___x_954_; size_t v___x_955_; 
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_949_, v___x_954_);
v_i_949_ = v___x_955_;
v_b_951_ = v___y_953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(lean_object* v_f_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_es_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_es_967_ = lean_ctor_get(v_x_965_, 0);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_array_get_size(v_es_967_);
v___x_970_ = lean_nat_dec_lt(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_dec(v_f_964_);
return v_x_966_;
}
else
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
v___x_971_ = ((size_t)0ULL);
v___x_972_ = lean_usize_of_nat(v___x_969_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_964_, v_es_967_, v___x_971_, v___x_972_, v_x_966_);
return v___x_973_;
}
}
else
{
lean_object* v_ks_974_; lean_object* v_vs_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_ks_974_ = lean_ctor_get(v_x_965_, 0);
v_vs_975_ = lean_ctor_get(v_x_965_, 1);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(v_f_964_, v_ks_974_, v_vs_975_, v___x_976_, v_x_966_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_f_978_, lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_978_, v_x_979_, v_x_980_);
lean_dec_ref(v_x_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg___boxed(lean_object* v_f_982_, lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; lean_object* v_res_989_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_982_, v_as_983_, v_i_boxed_987_, v_stop_boxed_988_, v_b_986_);
lean_dec_ref(v_as_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(lean_object* v_map_990_, lean_object* v_f_991_, lean_object* v_init_992_){
_start:
{
lean_object* v___f_993_; lean_object* v___x_994_; 
v___f_993_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___lam__0), 4, 1);
lean_closure_set(v___f_993_, 0, v_f_991_);
v___x_994_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v___f_993_, v_map_990_, v_init_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg___boxed(lean_object* v_map_995_, lean_object* v_f_996_, lean_object* v_init_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(v_map_995_, v_f_996_, v_init_997_);
lean_dec_ref(v_map_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object* v_o_1002_, lean_object* v_k_1003_, uint8_t v_v_1004_){
_start:
{
lean_object* v_map_1005_; uint8_t v_hasTrace_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1020_; 
v_map_1005_ = lean_ctor_get(v_o_1002_, 0);
v_hasTrace_1006_ = lean_ctor_get_uint8(v_o_1002_, sizeof(void*)*1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_o_1002_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1008_ = v_o_1002_;
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_map_1005_);
lean_dec(v_o_1002_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1010_, 0, v_v_1004_);
lean_inc(v_k_1003_);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1003_, v___x_1010_, v_map_1005_);
if (v_hasTrace_1006_ == 0)
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___closed__1));
v___x_1013_ = l_Lean_Name_isPrefixOf(v___x_1012_, v_k_1003_);
lean_dec(v_k_1003_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1011_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1011_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*1, v___x_1013_);
return v___x_1015_;
}
}
else
{
lean_object* v___x_1018_; 
lean_dec(v_k_1003_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1011_);
v___x_1018_ = v___x_1008_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1019_, sizeof(void*)*1, v_hasTrace_1006_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4___boxed(lean_object* v_o_1021_, lean_object* v_k_1022_, lean_object* v_v_1023_){
_start:
{
uint8_t v_v_boxed_1024_; lean_object* v_res_1025_; 
v_v_boxed_1024_ = lean_unbox(v_v_1023_);
v_res_1025_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(v_o_1021_, v_k_1022_, v_v_boxed_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object* v_opts_1026_, lean_object* v_opt_1027_, uint8_t v_val_1028_){
_start:
{
lean_object* v_name_1029_; lean_object* v___x_1030_; 
v_name_1029_ = lean_ctor_get(v_opt_1027_, 0);
lean_inc(v_name_1029_);
lean_dec_ref(v_opt_1027_);
v___x_1030_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(v_opts_1026_, v_name_1029_, v_val_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object* v_opts_1031_, lean_object* v_opt_1032_, lean_object* v_val_1033_){
_start:
{
uint8_t v_val_boxed_1034_; lean_object* v_res_1035_; 
v_val_boxed_1034_ = lean_unbox(v_val_1033_);
v_res_1035_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_opts_1031_, v_opt_1032_, v_val_boxed_1034_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_ref_1042_; lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_ref_1042_ = lean_ctor_get(v___y_1039_, 2);
v___x_1043_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_inc(v_ref_1042_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_ref_1042_);
lean_ctor_set(v___x_1048_, 1, v_a_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg___boxed(lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(lean_object* v_ref_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_toCold_1067_; lean_object* v_currRecDepth_1068_; lean_object* v_ref_1069_; uint8_t v_diag_1070_; uint8_t v_suppressElabErrors_1071_; lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_toCold_1067_ = lean_ctor_get(v___y_1064_, 0);
v_currRecDepth_1068_ = lean_ctor_get(v___y_1064_, 1);
v_ref_1069_ = lean_ctor_get(v___y_1064_, 2);
v_diag_1070_ = lean_ctor_get_uint8(v___y_1064_, sizeof(void*)*3);
v_suppressElabErrors_1071_ = lean_ctor_get_uint8(v___y_1064_, sizeof(void*)*3 + 1);
v_ref_1072_ = l_Lean_replaceRef(v_ref_1060_, v_ref_1069_);
lean_inc(v_currRecDepth_1068_);
lean_inc_ref(v_toCold_1067_);
v___x_1073_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1073_, 0, v_toCold_1067_);
lean_ctor_set(v___x_1073_, 1, v_currRecDepth_1068_);
lean_ctor_set(v___x_1073_, 2, v_ref_1072_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*3, v_diag_1070_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*3 + 1, v_suppressElabErrors_1071_);
v___x_1074_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_1061_, v___y_1062_, v___y_1063_, v___x_1073_, v___y_1065_);
lean_dec_ref_known(v___x_1073_, 3);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg___boxed(lean_object* v_ref_1075_, lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(v_ref_1075_, v_msg_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_ref_1075_);
return v_res_1082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__0);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
lean_ctor_set(v___x_1088_, 2, v___x_1087_);
lean_ctor_set(v___x_1088_, 3, v___x_1087_);
lean_ctor_set(v___x_1088_, 4, v___x_1086_);
lean_ctor_set(v___x_1088_, 5, v___x_1086_);
lean_ctor_set(v___x_1088_, 6, v___x_1086_);
lean_ctor_set(v___x_1088_, 7, v___x_1086_);
lean_ctor_set(v___x_1088_, 8, v___x_1086_);
lean_ctor_set(v___x_1088_, 9, v___x_1086_);
lean_ctor_set(v___x_1088_, 10, v___x_1086_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_unsigned_to_nat(32u);
v___x_1090_ = lean_mk_empty_array_with_capacity(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1092_ = ((size_t)5ULL);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_unsigned_to_nat(32u);
v___x_1095_ = lean_mk_empty_array_with_capacity(v___x_1094_);
v___x_1096_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__3);
v___x_1097_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1095_);
lean_ctor_set(v___x_1097_, 2, v___x_1093_);
lean_ctor_set(v___x_1097_, 3, v___x_1093_);
lean_ctor_set_usize(v___x_1097_, 4, v___x_1092_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = lean_box(1);
v___x_1099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__4);
v___x_1100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__1);
v___x_1101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v___x_1098_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__6));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__8));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__10));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__12));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__14));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__16));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__18));
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(lean_object* v_msg_1123_, lean_object* v_declHint_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_env_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = l_Lean_Name_isAnonymous(v_declHint_1124_);
if (v___x_1129_ == 0)
{
uint8_t v_isExporting_1130_; 
v_isExporting_1130_ = lean_ctor_get_uint8(v_env_1128_, sizeof(void*)*8);
if (v_isExporting_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_env_1128_);
lean_dec(v_declHint_1124_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_msg_1123_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
lean_inc_ref(v_env_1128_);
v___x_1132_ = l_Lean_Environment_setExporting(v_env_1128_, v___x_1129_);
lean_inc(v_declHint_1124_);
lean_inc_ref(v___x_1132_);
v___x_1133_ = l_Lean_Environment_contains(v___x_1132_, v_declHint_1124_, v_isExporting_1130_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_env_1128_);
lean_dec(v_declHint_1124_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_msg_1123_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_c_1140_; lean_object* v___x_1141_; 
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__2);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__5);
v___x_1137_ = l_Lean_Options_empty;
v___x_1138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1132_);
lean_ctor_set(v___x_1138_, 1, v___x_1135_);
lean_ctor_set(v___x_1138_, 2, v___x_1136_);
lean_ctor_set(v___x_1138_, 3, v___x_1137_);
lean_inc(v_declHint_1124_);
v___x_1139_ = l_Lean_MessageData_ofConstName(v_declHint_1124_, v___x_1129_);
v_c_1140_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1140_, 0, v___x_1138_);
lean_ctor_set(v_c_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1128_, v_declHint_1124_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_env_1128_);
lean_dec(v_declHint_1124_);
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_c_1140_);
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__9);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_MessageData_note(v___x_1145_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_msg_1123_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
else
{
lean_object* v_val_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1184_; 
v_val_1149_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1151_ = v___x_1141_;
v_isShared_1152_ = v_isSharedCheck_1184_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_val_1149_);
lean_dec(v___x_1141_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1184_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_mod_1156_; uint8_t v___x_1157_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = l_Lean_Environment_header(v_env_1128_);
lean_dec_ref(v_env_1128_);
v___x_1155_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1154_);
v_mod_1156_ = lean_array_get(v___x_1153_, v___x_1155_, v_val_1149_);
lean_dec(v_val_1149_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = l_Lean_isPrivateName(v_declHint_1124_);
lean_dec(v_declHint_1124_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__11);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v_c_1140_);
v___x_1160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__13);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_MessageData_ofName(v_mod_1156_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_MessageData_note(v___x_1165_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_msg_1123_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1167_);
v___x_1169_ = v___x_1151_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__7);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_c_1140_);
v___x_1173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__17);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_MessageData_ofName(v_mod_1156_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__19);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_MessageData_note(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_msg_1123_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1180_);
v___x_1182_ = v___x_1151_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1185_; 
lean_dec_ref(v_env_1128_);
lean_dec(v_declHint_1124_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_msg_1123_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___boxed(lean_object* v_msg_1186_, lean_object* v_declHint_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_1186_, v_declHint_1187_, v___y_1188_);
lean_dec(v___y_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(lean_object* v_msg_1191_, lean_object* v_declHint_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v___x_1198_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_1191_, v_declHint_1192_, v___y_1196_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = l_Lean_unknownIdentifierMessageTag;
v___x_1204_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17___boxed(lean_object* v_msg_1209_, lean_object* v_declHint_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(v_msg_1209_, v_declHint_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(lean_object* v_ref_1217_, lean_object* v_msg_1218_, lean_object* v_declHint_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v_a_1226_; lean_object* v___x_1227_; 
v___x_1225_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17(v_msg_1218_, v_declHint_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
v___x_1227_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(v_ref_1217_, v_a_1226_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg___boxed(lean_object* v_ref_1228_, lean_object* v_msg_1229_, lean_object* v_declHint_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(v_ref_1228_, v_msg_1229_, v_declHint_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v_ref_1228_);
return v_res_1236_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__0));
v___x_1239_ = l_Lean_stringToMessageData(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__2));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_ref_1243_, lean_object* v_constName_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1250_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__1);
v___x_1251_ = 0;
lean_inc(v_constName_1244_);
v___x_1252_ = l_Lean_MessageData_ofConstName(v_constName_1244_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1250_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(v_ref_1243_, v___x_1255_, v_constName_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___boxed(lean_object* v_ref_1257_, lean_object* v_constName_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_1257_, v_constName_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_ref_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_ref_1271_; lean_object* v___x_1272_; 
v_ref_1271_ = lean_ctor_get(v___y_1268_, 2);
v___x_1272_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_1271_, v_constName_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_constName_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(v_constName_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object* v_constName_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; lean_object* v_env_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_st_ref_get(v___y_1284_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_env_1287_);
lean_dec(v___x_1286_);
v___x_1288_ = 0;
lean_inc(v_constName_1280_);
v___x_1289_ = l_Lean_Environment_findConstVal_x3f(v_env_1287_, v_constName_1280_, v___x_1288_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(v_constName_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1290_;
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_constName_1280_);
v_val_1291_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1289_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v___x_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 0);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_val_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object* v_constName_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_constName_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__1(lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
if (lean_obj_tag(v_a_1306_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = l_List_reverse___redArg(v_a_1307_);
return v___x_1308_;
}
else
{
lean_object* v_head_1309_; lean_object* v_tail_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1319_; 
v_head_1309_ = lean_ctor_get(v_a_1306_, 0);
v_tail_1310_ = lean_ctor_get(v_a_1306_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1306_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1312_ = v_a_1306_;
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_tail_1310_);
lean_inc(v_head_1309_);
lean_dec(v_a_1306_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_Lean_mkLevelParam(v_head_1309_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v_a_1307_);
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_a_1307_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v_a_1306_ = v_tail_1310_;
v_a_1307_ = v___x_1316_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object* v_constName_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
lean_inc(v_constName_1320_);
v___x_1326_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_constName_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1338_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1338_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1338_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_levelParams_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v_levelParams_1331_ = lean_ctor_get(v_a_1327_, 1);
lean_inc(v_levelParams_1331_);
lean_dec(v_a_1327_);
v___x_1332_ = lean_box(0);
v___x_1333_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__1(v_levelParams_1331_, v___x_1332_);
v___x_1334_ = l_Lean_mkConst(v_constName_1320_, v___x_1333_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1334_);
v___x_1336_ = v___x_1329_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_constName_1320_);
v_a_1339_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1326_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1326_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object* v_constName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_constName_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(lean_object* v_as_1356_, size_t v_i_1357_, size_t v_stop_1358_, lean_object* v_b_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_usize_dec_eq(v_i_1357_, v_stop_1358_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_array_uget_borrowed(v_as_1356_, v_i_1357_);
lean_inc(v___x_1366_);
v___x_1367_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v___x_1366_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc_n(v_a_1368_, 2);
lean_dec_ref_known(v___x_1367_, 1);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
v___x_1369_ = lean_infer_type(v_a_1368_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = l_Lean_Meta_isClass_x3f(v_a_1370_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v_a_1374_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___closed__0));
v___x_1379_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_a_1372_, v___x_1378_);
lean_dec(v_a_1372_);
if (v___x_1379_ == 0)
{
lean_dec(v_a_1368_);
v_a_1374_ = v_b_1359_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1380_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3);
v___x_1381_ = l_Lean_MessageData_ofConst(v_a_1368_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1380_);
v___x_1384_ = lean_array_push(v_b_1359_, v___x_1383_);
v_a_1374_ = v___x_1384_;
goto v___jp_1373_;
}
v___jp_1373_:
{
size_t v___x_1375_; size_t v___x_1376_; 
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1357_, v___x_1375_);
v_i_1357_ = v___x_1376_;
v_b_1359_ = v_a_1374_;
goto _start;
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_a_1368_);
lean_dec_ref(v_b_1359_);
v_a_1385_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1371_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1371_);
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
lean_dec(v_a_1368_);
lean_dec_ref(v_b_1359_);
v_a_1393_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1369_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1369_);
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
lean_dec_ref(v_b_1359_);
v_a_1401_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1367_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1367_);
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
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_b_1359_);
return v___x_1409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9___boxed(lean_object* v_as_1410_, lean_object* v_i_1411_, lean_object* v_stop_1412_, lean_object* v_b_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
size_t v_i_boxed_1419_; size_t v_stop_boxed_1420_; lean_object* v_res_1421_; 
v_i_boxed_1419_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_stop_boxed_1420_ = lean_unbox_usize(v_stop_1412_);
lean_dec(v_stop_1412_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_as_1410_, v_i_boxed_1419_, v_stop_boxed_1420_, v_b_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_as_1410_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object* v_as_1424_, lean_object* v_start_1425_, lean_object* v_stop_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___closed__0));
v___x_1433_ = lean_nat_dec_lt(v_start_1425_, v_stop_1426_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_array_get_size(v_as_1424_);
v___x_1436_ = lean_nat_dec_le(v_stop_1426_, v___x_1435_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_lt(v_start_1425_, v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1432_);
return v___x_1438_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_usize_of_nat(v_start_1425_);
v___x_1440_ = lean_usize_of_nat(v___x_1435_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_as_1424_, v___x_1439_, v___x_1440_, v___x_1432_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1441_;
}
}
else
{
size_t v___x_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_usize_of_nat(v_start_1425_);
v___x_1443_ = lean_usize_of_nat(v_stop_1426_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__9(v_as_1424_, v___x_1442_, v___x_1443_, v___x_1432_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object* v_as_1445_, lean_object* v_start_1446_, lean_object* v_stop_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v_as_1445_, v_start_1446_, v_stop_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v_stop_1447_);
lean_dec(v_start_1446_);
lean_dec_ref(v_as_1445_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(lean_object* v_hi_1454_, lean_object* v_pivot_1455_, lean_object* v_as_1456_, lean_object* v_i_1457_, lean_object* v_k_1458_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_nat_dec_lt(v_k_1458_, v_hi_1454_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec(v_k_1458_);
v___x_1460_ = lean_array_fswap(v_as_1456_, v_i_1457_, v_hi_1454_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_i_1457_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = lean_array_fget_borrowed(v_as_1456_, v_k_1458_);
v___x_1463_ = l_Lean_Name_lt(v___x_1462_, v_pivot_1455_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_k_1458_, v___x_1464_);
lean_dec(v_k_1458_);
v_k_1458_ = v___x_1465_;
goto _start;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_array_fswap(v_as_1456_, v_i_1457_, v_k_1458_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v_i_1457_, v___x_1468_);
lean_dec(v_i_1457_);
v___x_1470_ = lean_nat_add(v_k_1458_, v___x_1468_);
lean_dec(v_k_1458_);
v_as_1456_ = v___x_1467_;
v_i_1457_ = v___x_1469_;
v_k_1458_ = v___x_1470_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg___boxed(lean_object* v_hi_1472_, lean_object* v_pivot_1473_, lean_object* v_as_1474_, lean_object* v_i_1475_, lean_object* v_k_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(v_hi_1472_, v_pivot_1473_, v_as_1474_, v_i_1475_, v_k_1476_);
lean_dec(v_pivot_1473_);
lean_dec(v_hi_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(lean_object* v_n_1478_, lean_object* v_as_1479_, lean_object* v_lo_1480_, lean_object* v_hi_1481_){
_start:
{
lean_object* v___y_1483_; uint8_t v___x_1493_; 
v___x_1493_ = lean_nat_dec_lt(v_lo_1480_, v_hi_1481_);
if (v___x_1493_ == 0)
{
lean_dec(v_lo_1480_);
return v_as_1479_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_mid_1496_; lean_object* v___y_1498_; lean_object* v___y_1504_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1494_ = lean_nat_add(v_lo_1480_, v_hi_1481_);
v___x_1495_ = lean_unsigned_to_nat(1u);
v_mid_1496_ = lean_nat_shiftr(v___x_1494_, v___x_1495_);
lean_dec(v___x_1494_);
v___x_1509_ = lean_array_fget_borrowed(v_as_1479_, v_mid_1496_);
v___x_1510_ = lean_array_fget_borrowed(v_as_1479_, v_lo_1480_);
v___x_1511_ = l_Lean_Name_lt(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
v___y_1504_ = v_as_1479_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_array_fswap(v_as_1479_, v_lo_1480_, v_mid_1496_);
v___y_1504_ = v___x_1512_;
goto v___jp_1503_;
}
v___jp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_array_fget_borrowed(v___y_1498_, v_mid_1496_);
v___x_1500_ = lean_array_fget_borrowed(v___y_1498_, v_hi_1481_);
v___x_1501_ = l_Lean_Name_lt(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec(v_mid_1496_);
v___y_1483_ = v___y_1498_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_array_fswap(v___y_1498_, v_mid_1496_, v_hi_1481_);
lean_dec(v_mid_1496_);
v___y_1483_ = v___x_1502_;
goto v___jp_1482_;
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_array_fget_borrowed(v___y_1504_, v_hi_1481_);
v___x_1506_ = lean_array_fget_borrowed(v___y_1504_, v_lo_1480_);
v___x_1507_ = l_Lean_Name_lt(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
v___y_1498_ = v___y_1504_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_array_fswap(v___y_1504_, v_lo_1480_, v_hi_1481_);
v___y_1498_ = v___x_1508_;
goto v___jp_1497_;
}
}
}
v___jp_1482_:
{
lean_object* v_pivot_1484_; lean_object* v___x_1485_; lean_object* v_fst_1486_; lean_object* v_snd_1487_; uint8_t v___x_1488_; 
v_pivot_1484_ = lean_array_fget(v___y_1483_, v_hi_1481_);
lean_inc_n(v_lo_1480_, 2);
v___x_1485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(v_hi_1481_, v_pivot_1484_, v___y_1483_, v_lo_1480_, v_lo_1480_);
lean_dec(v_pivot_1484_);
v_fst_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_fst_1486_);
v_snd_1487_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_snd_1487_);
lean_dec_ref(v___x_1485_);
v___x_1488_ = lean_nat_dec_le(v_hi_1481_, v_fst_1486_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_n_1478_, v_snd_1487_, v_lo_1480_, v_fst_1486_);
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_add(v_fst_1486_, v___x_1490_);
lean_dec(v_fst_1486_);
v_as_1479_ = v___x_1489_;
v_lo_1480_ = v___x_1491_;
goto _start;
}
else
{
lean_dec(v_fst_1486_);
lean_dec(v_lo_1480_);
return v_snd_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(lean_object* v_n_1513_, lean_object* v_as_1514_, lean_object* v_lo_1515_, lean_object* v_hi_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_n_1513_, v_as_1514_, v_lo_1515_, v_hi_1516_);
lean_dec(v_hi_1516_);
lean_dec(v_n_1513_);
return v_res_1517_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2);
v___x_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
lean_ctor_set(v___x_1524_, 3, v___x_1523_);
lean_ctor_set(v___x_1524_, 4, v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object* v___f_1530_, lean_object* v_s_1531_, uint8_t v___x_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___x_1629_; lean_object* v_toCold_1630_; lean_object* v_currRecDepth_1631_; lean_object* v_ref_1632_; uint8_t v_suppressElabErrors_1633_; lean_object* v_fileName_1634_; lean_object* v_fileMap_1635_; lean_object* v_options_1636_; lean_object* v_currNamespace_1637_; lean_object* v_openDecls_1638_; lean_object* v_initHeartbeats_1639_; lean_object* v_maxHeartbeats_1640_; lean_object* v_quotContext_1641_; lean_object* v_currMacroScope_1642_; lean_object* v_cancelTk_x3f_1643_; lean_object* v_inheritedTraceOptions_1644_; lean_object* v_env_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v_fileName_1650_; lean_object* v_fileMap_1651_; lean_object* v_currNamespace_1652_; lean_object* v_openDecls_1653_; lean_object* v_initHeartbeats_1654_; lean_object* v_maxHeartbeats_1655_; lean_object* v_quotContext_1656_; lean_object* v_currMacroScope_1657_; lean_object* v_cancelTk_x3f_1658_; lean_object* v_inheritedTraceOptions_1659_; lean_object* v_currRecDepth_1660_; lean_object* v_ref_1661_; uint8_t v_suppressElabErrors_1662_; lean_object* v___y_1663_; uint8_t v___y_1695_; uint8_t v___x_1716_; 
v___x_1629_ = lean_st_ref_get(v___y_1536_);
v_toCold_1630_ = lean_ctor_get(v___y_1535_, 0);
v_currRecDepth_1631_ = lean_ctor_get(v___y_1535_, 1);
v_ref_1632_ = lean_ctor_get(v___y_1535_, 2);
v_suppressElabErrors_1633_ = lean_ctor_get_uint8(v___y_1535_, sizeof(void*)*3 + 1);
v_fileName_1634_ = lean_ctor_get(v_toCold_1630_, 0);
v_fileMap_1635_ = lean_ctor_get(v_toCold_1630_, 1);
v_options_1636_ = lean_ctor_get(v_toCold_1630_, 2);
v_currNamespace_1637_ = lean_ctor_get(v_toCold_1630_, 4);
v_openDecls_1638_ = lean_ctor_get(v_toCold_1630_, 5);
v_initHeartbeats_1639_ = lean_ctor_get(v_toCold_1630_, 6);
v_maxHeartbeats_1640_ = lean_ctor_get(v_toCold_1630_, 7);
v_quotContext_1641_ = lean_ctor_get(v_toCold_1630_, 8);
v_currMacroScope_1642_ = lean_ctor_get(v_toCold_1630_, 9);
v_cancelTk_x3f_1643_ = lean_ctor_get(v_toCold_1630_, 10);
v_inheritedTraceOptions_1644_ = lean_ctor_get(v_toCold_1630_, 11);
v_env_1645_ = lean_ctor_get(v___x_1629_, 0);
lean_inc_ref(v_env_1645_);
lean_dec(v___x_1629_);
v___x_1646_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1636_);
v___x_1647_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_options_1636_, v___x_1646_, v___x_1532_);
v___x_1648_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_1647_, v___x_1646_);
v___x_1716_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1645_);
lean_dec_ref(v_env_1645_);
if (v___x_1648_ == 0)
{
if (v___x_1716_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1644_);
lean_inc(v_cancelTk_x3f_1643_);
lean_inc(v_currMacroScope_1642_);
lean_inc(v_quotContext_1641_);
lean_inc(v_maxHeartbeats_1640_);
lean_inc(v_initHeartbeats_1639_);
lean_inc(v_openDecls_1638_);
lean_inc(v_currNamespace_1637_);
lean_inc_ref(v_fileMap_1635_);
lean_inc_ref(v_fileName_1634_);
v_fileName_1650_ = v_fileName_1634_;
v_fileMap_1651_ = v_fileMap_1635_;
v_currNamespace_1652_ = v_currNamespace_1637_;
v_openDecls_1653_ = v_openDecls_1638_;
v_initHeartbeats_1654_ = v_initHeartbeats_1639_;
v_maxHeartbeats_1655_ = v_maxHeartbeats_1640_;
v_quotContext_1656_ = v_quotContext_1641_;
v_currMacroScope_1657_ = v_currMacroScope_1642_;
v_cancelTk_x3f_1658_ = v_cancelTk_x3f_1643_;
v_inheritedTraceOptions_1659_ = v_inheritedTraceOptions_1644_;
v_currRecDepth_1660_ = v_currRecDepth_1631_;
v_ref_1661_ = v_ref_1632_;
v_suppressElabErrors_1662_ = v_suppressElabErrors_1633_;
v___y_1663_ = v___y_1536_;
goto v___jp_1649_;
}
else
{
v___y_1695_ = v___x_1648_;
goto v___jp_1694_;
}
}
else
{
v___y_1695_ = v___x_1716_;
goto v___jp_1694_;
}
v___jp_1538_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_array_get_size(v___y_1543_);
v___x_1545_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v___y_1543_, v___y_1540_, v___x_1544_, v___y_1533_, v___y_1534_, v___y_1542_, v___y_1539_);
lean_dec_ref(v___y_1542_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1543_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___y_1541_);
lean_ctor_set(v___x_1550_, 1, v_a_1546_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v___y_1541_);
v_a_1555_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1545_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1545_);
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
v___jp_1563_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v___y_1567_, v___y_1564_, v___y_1565_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec(v___y_1567_);
v___y_1539_ = v___y_1566_;
v___y_1540_ = v___y_1568_;
v___y_1541_ = v___y_1569_;
v___y_1542_ = v___y_1570_;
v___y_1543_ = v___x_1572_;
goto v___jp_1538_;
}
v___jp_1573_:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_le(v___y_1581_, v___y_1576_);
if (v___x_1582_ == 0)
{
lean_dec(v___y_1576_);
lean_inc(v___y_1581_);
v___y_1564_ = v___y_1574_;
v___y_1565_ = v___y_1581_;
v___y_1566_ = v___y_1575_;
v___y_1567_ = v___y_1577_;
v___y_1568_ = v___y_1578_;
v___y_1569_ = v___y_1579_;
v___y_1570_ = v___y_1580_;
v___y_1571_ = v___y_1581_;
goto v___jp_1563_;
}
else
{
v___y_1564_ = v___y_1574_;
v___y_1565_ = v___y_1581_;
v___y_1566_ = v___y_1575_;
v___y_1567_ = v___y_1577_;
v___y_1568_ = v___y_1578_;
v___y_1569_ = v___y_1579_;
v___y_1570_ = v___y_1580_;
v___y_1571_ = v___y_1576_;
goto v___jp_1563_;
}
}
v___jp_1583_:
{
if (lean_obj_tag(v___y_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v_diag_1589_; lean_object* v_unfoldCounter_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_a_1587_ = lean_ctor_get(v___y_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___y_1586_, 1);
v___x_1588_ = lean_st_ref_get(v___y_1534_);
v_diag_1589_ = lean_ctor_get(v___x_1588_, 4);
lean_inc_ref(v_diag_1589_);
lean_dec(v___x_1588_);
v_unfoldCounter_1590_ = lean_ctor_get(v_diag_1589_, 0);
lean_inc_ref(v_unfoldCounter_1590_);
lean_dec_ref(v_diag_1589_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_1593_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(v_unfoldCounter_1590_, v___f_1530_, v___x_1592_);
lean_dec_ref(v_unfoldCounter_1590_);
v___x_1594_ = lean_array_get_size(v___x_1593_);
v___x_1595_ = lean_nat_dec_eq(v___x_1594_, v___x_1591_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_sub(v___x_1594_, v___x_1596_);
v___x_1598_ = lean_nat_dec_le(v___x_1591_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_inc(v___x_1597_);
v___y_1574_ = v___x_1593_;
v___y_1575_ = v___y_1584_;
v___y_1576_ = v___x_1597_;
v___y_1577_ = v___x_1594_;
v___y_1578_ = v___x_1591_;
v___y_1579_ = v_a_1587_;
v___y_1580_ = v___y_1585_;
v___y_1581_ = v___x_1597_;
goto v___jp_1573_;
}
else
{
v___y_1574_ = v___x_1593_;
v___y_1575_ = v___y_1584_;
v___y_1576_ = v___x_1597_;
v___y_1577_ = v___x_1594_;
v___y_1578_ = v___x_1591_;
v___y_1579_ = v_a_1587_;
v___y_1580_ = v___y_1585_;
v___y_1581_ = v___x_1591_;
goto v___jp_1573_;
}
}
else
{
v___y_1539_ = v___y_1584_;
v___y_1540_ = v___x_1591_;
v___y_1541_ = v_a_1587_;
v___y_1542_ = v___y_1585_;
v___y_1543_ = v___x_1593_;
goto v___jp_1538_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v___f_1530_);
v_a_1599_ = lean_ctor_get(v___y_1586_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___y_1586_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___y_1586_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___y_1586_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
v___jp_1607_:
{
lean_object* v___x_1610_; uint8_t v_transparency_1611_; uint8_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1610_ = l_Lean_Meta_Context_config(v___y_1533_);
v_transparency_1611_ = lean_ctor_get_uint8(v___x_1610_, 9);
lean_dec_ref(v___x_1610_);
v___x_1612_ = 1;
v___x_1613_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc_ref(v___y_1609_);
v___x_1614_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1531_, v___y_1533_, v___y_1534_, v___y_1609_, v___y_1608_);
v___y_1584_ = v___y_1608_;
v___y_1585_ = v___y_1609_;
v___y_1586_ = v___x_1614_;
goto v___jp_1583_;
}
else
{
lean_object* v_keyedConfig_1615_; uint8_t v_trackZetaDelta_1616_; lean_object* v_zetaDeltaSet_1617_; lean_object* v_lctx_1618_; lean_object* v_localInstances_1619_; lean_object* v_defEqCtx_x3f_1620_; lean_object* v_synthPendingDepth_1621_; lean_object* v_customCanUnfoldPredicate_x3f_1622_; uint8_t v_univApprox_1623_; uint8_t v_inTypeClassResolution_1624_; uint8_t v_cacheInferType_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_keyedConfig_1615_ = lean_ctor_get(v___y_1533_, 0);
v_trackZetaDelta_1616_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*7);
v_zetaDeltaSet_1617_ = lean_ctor_get(v___y_1533_, 1);
v_lctx_1618_ = lean_ctor_get(v___y_1533_, 2);
v_localInstances_1619_ = lean_ctor_get(v___y_1533_, 3);
v_defEqCtx_x3f_1620_ = lean_ctor_get(v___y_1533_, 4);
v_synthPendingDepth_1621_ = lean_ctor_get(v___y_1533_, 5);
v_customCanUnfoldPredicate_x3f_1622_ = lean_ctor_get(v___y_1533_, 6);
v_univApprox_1623_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1624_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*7 + 2);
v_cacheInferType_1625_ = lean_ctor_get_uint8(v___y_1533_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1615_);
v___x_1626_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1612_, v_keyedConfig_1615_);
lean_inc(v_customCanUnfoldPredicate_x3f_1622_);
lean_inc(v_synthPendingDepth_1621_);
lean_inc(v_defEqCtx_x3f_1620_);
lean_inc_ref(v_localInstances_1619_);
lean_inc_ref(v_lctx_1618_);
lean_inc(v_zetaDeltaSet_1617_);
v___x_1627_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_zetaDeltaSet_1617_);
lean_ctor_set(v___x_1627_, 2, v_lctx_1618_);
lean_ctor_set(v___x_1627_, 3, v_localInstances_1619_);
lean_ctor_set(v___x_1627_, 4, v_defEqCtx_x3f_1620_);
lean_ctor_set(v___x_1627_, 5, v_synthPendingDepth_1621_);
lean_ctor_set(v___x_1627_, 6, v_customCanUnfoldPredicate_x3f_1622_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*7, v_trackZetaDelta_1616_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*7 + 1, v_univApprox_1623_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1624_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*7 + 3, v_cacheInferType_1625_);
lean_inc_ref(v___y_1609_);
v___x_1628_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1531_, v___x_1627_, v___y_1534_, v___y_1609_, v___y_1608_);
lean_dec_ref_known(v___x_1627_, 7);
v___y_1584_ = v___y_1608_;
v___y_1585_ = v___y_1609_;
v___y_1586_ = v___x_1628_;
goto v___jp_1583_;
}
}
v___jp_1649_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1664_ = l_Lean_maxRecDepth;
v___x_1665_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v___x_1647_, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1666_, 0, v_fileName_1650_);
lean_ctor_set(v___x_1666_, 1, v_fileMap_1651_);
lean_ctor_set(v___x_1666_, 2, v___x_1647_);
lean_ctor_set(v___x_1666_, 3, v___x_1665_);
lean_ctor_set(v___x_1666_, 4, v_currNamespace_1652_);
lean_ctor_set(v___x_1666_, 5, v_openDecls_1653_);
lean_ctor_set(v___x_1666_, 6, v_initHeartbeats_1654_);
lean_ctor_set(v___x_1666_, 7, v_maxHeartbeats_1655_);
lean_ctor_set(v___x_1666_, 8, v_quotContext_1656_);
lean_ctor_set(v___x_1666_, 9, v_currMacroScope_1657_);
lean_ctor_set(v___x_1666_, 10, v_cancelTk_x3f_1658_);
lean_ctor_set(v___x_1666_, 11, v_inheritedTraceOptions_1659_);
lean_inc(v_ref_1661_);
lean_inc(v_currRecDepth_1660_);
v___x_1667_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_currRecDepth_1660_);
lean_ctor_set(v___x_1667_, 2, v_ref_1661_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*3, v___x_1648_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*3 + 1, v_suppressElabErrors_1662_);
v___x_1668_ = l_Lean_isDiagnosticsEnabled___redArg(v___x_1667_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; uint8_t v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = lean_unbox(v_a_1669_);
lean_dec(v_a_1669_);
if (v___x_1670_ == 0)
{
v___y_1608_ = v___y_1663_;
v___y_1609_ = v___x_1667_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1671_; lean_object* v_mctx_1672_; lean_object* v_cache_1673_; lean_object* v_zetaDeltaFVarIds_1674_; lean_object* v_postponed_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1684_; 
v___x_1671_ = lean_st_ref_take(v___y_1534_);
v_mctx_1672_ = lean_ctor_get(v___x_1671_, 0);
v_cache_1673_ = lean_ctor_get(v___x_1671_, 1);
v_zetaDeltaFVarIds_1674_ = lean_ctor_get(v___x_1671_, 2);
v_postponed_1675_ = lean_ctor_get(v___x_1671_, 3);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v___x_1671_, 4);
lean_dec(v_unused_1685_);
v___x_1677_ = v___x_1671_;
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_postponed_1675_);
lean_inc(v_zetaDeltaFVarIds_1674_);
lean_inc(v_cache_1673_);
lean_inc(v_mctx_1672_);
lean_dec(v___x_1671_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 4, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_mctx_1672_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_cache_1673_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_zetaDeltaFVarIds_1674_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_postponed_1675_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_st_ref_put(v___y_1534_, v___x_1681_);
v___y_1608_ = v___y_1663_;
v___y_1609_ = v___x_1667_;
goto v___jp_1607_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref_known(v___x_1667_, 3);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_s_1531_);
lean_dec_ref(v___f_1530_);
v_a_1686_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1668_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1668_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
v___jp_1694_:
{
if (v___y_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v_env_1697_; lean_object* v_nextMacroScope_1698_; lean_object* v_ngen_1699_; lean_object* v_auxDeclNGen_1700_; lean_object* v_traceState_1701_; lean_object* v_messages_1702_; lean_object* v_infoState_1703_; lean_object* v_snapshotTasks_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1714_; 
v___x_1696_ = lean_st_ref_take(v___y_1536_);
v_env_1697_ = lean_ctor_get(v___x_1696_, 0);
v_nextMacroScope_1698_ = lean_ctor_get(v___x_1696_, 1);
v_ngen_1699_ = lean_ctor_get(v___x_1696_, 2);
v_auxDeclNGen_1700_ = lean_ctor_get(v___x_1696_, 3);
v_traceState_1701_ = lean_ctor_get(v___x_1696_, 4);
v_messages_1702_ = lean_ctor_get(v___x_1696_, 6);
v_infoState_1703_ = lean_ctor_get(v___x_1696_, 7);
v_snapshotTasks_1704_ = lean_ctor_get(v___x_1696_, 8);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v___x_1696_, 5);
lean_dec(v_unused_1715_);
v___x_1706_ = v___x_1696_;
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_snapshotTasks_1704_);
lean_inc(v_infoState_1703_);
lean_inc(v_messages_1702_);
lean_inc(v_traceState_1701_);
lean_inc(v_auxDeclNGen_1700_);
lean_inc(v_ngen_1699_);
lean_inc(v_nextMacroScope_1698_);
lean_inc(v_env_1697_);
lean_dec(v___x_1696_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1708_ = l_Lean_Kernel_enableDiag(v_env_1697_, v___x_1648_);
v___x_1709_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 5, v___x_1709_);
lean_ctor_set(v___x_1706_, 0, v___x_1708_);
v___x_1711_ = v___x_1706_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_nextMacroScope_1698_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_ngen_1699_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_auxDeclNGen_1700_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_traceState_1701_);
lean_ctor_set(v_reuseFailAlloc_1713_, 5, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1713_, 6, v_messages_1702_);
lean_ctor_set(v_reuseFailAlloc_1713_, 7, v_infoState_1703_);
lean_ctor_set(v_reuseFailAlloc_1713_, 8, v_snapshotTasks_1704_);
v___x_1711_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_st_ref_put(v___y_1536_, v___x_1711_);
lean_inc_ref(v_inheritedTraceOptions_1644_);
lean_inc(v_cancelTk_x3f_1643_);
lean_inc(v_currMacroScope_1642_);
lean_inc(v_quotContext_1641_);
lean_inc(v_maxHeartbeats_1640_);
lean_inc(v_initHeartbeats_1639_);
lean_inc(v_openDecls_1638_);
lean_inc(v_currNamespace_1637_);
lean_inc_ref(v_fileMap_1635_);
lean_inc_ref(v_fileName_1634_);
v_fileName_1650_ = v_fileName_1634_;
v_fileMap_1651_ = v_fileMap_1635_;
v_currNamespace_1652_ = v_currNamespace_1637_;
v_openDecls_1653_ = v_openDecls_1638_;
v_initHeartbeats_1654_ = v_initHeartbeats_1639_;
v_maxHeartbeats_1655_ = v_maxHeartbeats_1640_;
v_quotContext_1656_ = v_quotContext_1641_;
v_currMacroScope_1657_ = v_currMacroScope_1642_;
v_cancelTk_x3f_1658_ = v_cancelTk_x3f_1643_;
v_inheritedTraceOptions_1659_ = v_inheritedTraceOptions_1644_;
v_currRecDepth_1660_ = v_currRecDepth_1631_;
v_ref_1661_ = v_ref_1632_;
v_suppressElabErrors_1662_ = v_suppressElabErrors_1633_;
v___y_1663_ = v___y_1536_;
goto v___jp_1649_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1644_);
lean_inc(v_cancelTk_x3f_1643_);
lean_inc(v_currMacroScope_1642_);
lean_inc(v_quotContext_1641_);
lean_inc(v_maxHeartbeats_1640_);
lean_inc(v_initHeartbeats_1639_);
lean_inc(v_openDecls_1638_);
lean_inc(v_currNamespace_1637_);
lean_inc_ref(v_fileMap_1635_);
lean_inc_ref(v_fileName_1634_);
v_fileName_1650_ = v_fileName_1634_;
v_fileMap_1651_ = v_fileMap_1635_;
v_currNamespace_1652_ = v_currNamespace_1637_;
v_openDecls_1653_ = v_openDecls_1638_;
v_initHeartbeats_1654_ = v_initHeartbeats_1639_;
v_maxHeartbeats_1655_ = v_maxHeartbeats_1640_;
v_quotContext_1656_ = v_quotContext_1641_;
v_currMacroScope_1657_ = v_currMacroScope_1642_;
v_cancelTk_x3f_1658_ = v_cancelTk_x3f_1643_;
v_inheritedTraceOptions_1659_ = v_inheritedTraceOptions_1644_;
v_currRecDepth_1660_ = v_currRecDepth_1631_;
v_ref_1661_ = v_ref_1632_;
v_suppressElabErrors_1662_ = v_suppressElabErrors_1633_;
v___y_1663_ = v___y_1536_;
goto v___jp_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object* v___f_1717_, lean_object* v_s_1718_, lean_object* v___x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_11080__boxed_1725_; lean_object* v_res_1726_; 
v___x_11080__boxed_1725_ = lean_unbox(v___x_1719_);
v_res_1726_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(v___f_1717_, v_s_1718_, v___x_11080__boxed_1725_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
return v_res_1726_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1));
v___x_1730_ = l_Lean_stringToMessageData(v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3));
v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5));
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7));
v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
return v___x_1739_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14));
v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
return v___x_1751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16));
v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18));
v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20));
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34));
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* v_tacticName_1800_, lean_object* v_expectedType_1801_, lean_object* v_s_1802_, lean_object* v_r_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__8));
v___x_1810_ = l_Lean_Expr_isConstOf(v_r_1803_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___f_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; 
lean_dec_ref(v_expectedType_1801_);
v___f_1811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0));
v___x_1812_ = 1;
v___x_1813_ = lean_box(v___x_1812_);
lean_inc_ref(v_s_1802_);
v___f_1814_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1814_, 0, v___f_1811_);
lean_closure_set(v___f_1814_, 1, v_s_1802_);
lean_closure_set(v___f_1814_, 2, v___x_1813_);
v___x_1815_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__7___redArg(v___f_1814_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1929_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1929_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1929_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1928_; 
v_fst_1847_ = lean_ctor_get(v_a_1816_, 0);
v_snd_1848_ = lean_ctor_get(v_a_1816_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_a_1816_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1850_ = v_a_1816_;
v_isShared_1851_ = v_isSharedCheck_1928_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snd_1848_);
lean_inc(v_fst_1847_);
lean_dec(v_a_1816_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1928_;
goto v_resetjp_1849_;
}
v___jp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1823_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1824_ = l_Lean_MessageData_ofName(v_tacticName_1800_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_Expr_setPPExplicit(v_s_1802_, v___x_1812_);
v___x_1829_ = l_Lean_indentExpr(v___x_1828_);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1827_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_1834_ = l_Lean_MessageData_ofConstName(v___x_1833_, v___x_1810_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1832_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_MessageData_ofConstName(v___x_1809_, v___x_1810_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___y_1821_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___y_1822_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1843_);
v___x_1845_ = v___x_1818_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
v_resetjp_1849_:
{
lean_object* v___y_1853_; lean_object* v___y_1905_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = lean_array_get_size(v_snd_1848_);
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_nat_dec_eq(v___x_1918_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_nat_dec_eq(v___x_1918_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42));
v___y_1905_ = v___x_1923_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1924_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43));
v___y_1905_ = v___x_1924_;
goto v___jp_1904_;
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_snd_1848_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45);
lean_inc(v_fst_1847_);
v___x_1926_ = l_Lean_indentExpr(v_fst_1847_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___y_1853_ = v___x_1927_;
goto v___jp_1852_;
}
v___jp_1852_:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10));
v___x_1855_ = l_Lean_Expr_isAppOf(v_fst_1847_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13));
v___x_1857_ = l_Lean_Expr_isAppOf(v_fst_1847_, v___x_1856_);
lean_dec(v_fst_1847_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_del_object(v___x_1850_);
v___x_1858_ = l_Lean_MessageData_nil;
v___y_1821_ = v___y_1853_;
v___y_1822_ = v___x_1858_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1859_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15);
v___x_1860_ = l_Lean_MessageData_ofConstName(v___x_1856_, v___x_1855_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 7);
lean_ctor_set(v___x_1850_, 1, v___x_1860_);
lean_ctor_set(v___x_1850_, 0, v___x_1859_);
v___x_1862_ = v___x_1850_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4));
v___x_1866_ = l_Lean_MessageData_ofConstName(v___x_1865_, v___x_1855_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1864_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
lean_inc(v_tacticName_1800_);
v___x_1870_ = l_Lean_MessageData_ofName(v_tacticName_1800_);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23));
v___x_1875_ = l_Lean_MessageData_ofConstName(v___x_1874_, v___x_1855_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg___closed__15);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_MessageData_hint_x27(v___x_1878_);
v___y_1821_ = v___y_1853_;
v___y_1822_ = v___x_1879_;
goto v___jp_1820_;
}
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_dec(v_fst_1847_);
v___x_1881_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25);
v___x_1882_ = l_Lean_MessageData_ofConstName(v___x_1854_, v___x_1810_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 7);
lean_ctor_set(v___x_1850_, 1, v___x_1882_);
lean_ctor_set(v___x_1850_, 0, v___x_1881_);
v___x_1884_ = v___x_1850_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__4));
v___x_1888_ = l_Lean_MessageData_ofConstName(v___x_1887_, v___x_1810_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1886_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31));
v___x_1893_ = l_Lean_MessageData_ofConstName(v___x_1892_, v___x_1810_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1891_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33));
v___x_1898_ = l_Lean_MessageData_ofConstName(v___x_1897_, v___x_1810_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1896_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = l_Lean_MessageData_hint_x27(v___x_1901_);
v___y_1821_ = v___y_1853_;
v___y_1822_ = v___x_1902_;
goto v___jp_1820_;
}
}
}
v___jp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1906_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37);
lean_inc_ref(v___y_1905_);
v___x_1907_ = l_Lean_stringToMessageData(v___y_1905_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_array_to_list(v_snd_1848_);
v___x_1912_ = l_Lean_MessageData_andList(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1910_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
lean_inc(v_fst_1847_);
v___x_1916_ = l_Lean_indentExpr(v_fst_1847_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___y_1853_ = v___x_1917_;
goto v___jp_1852_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_s_1802_);
lean_dec(v_tacticName_1800_);
v_a_1930_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1815_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1815_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec_ref(v_s_1802_);
v___x_1938_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1939_ = l_Lean_MessageData_ofName(v_tacticName_1800_);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_indentExpr(v_expectedType_1801_);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
return v___x_1947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object* v_tacticName_1948_, lean_object* v_expectedType_1949_, lean_object* v_s_1950_, lean_object* v_r_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_1948_, v_expectedType_1949_, v_s_1950_, v_r_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec_ref(v_r_1951_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object* v_00_u03c3_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_map_1960_, lean_object* v_f_1961_, lean_object* v_init_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___redArg(v_map_1960_, v_f_1961_, v_init_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object* v_00_u03c3_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_map_1966_, lean_object* v_f_1967_, lean_object* v_init_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v_00_u03c3_1964_, v_00_u03b2_1965_, v_map_1966_, v_f_1967_, v_init_1968_);
lean_dec_ref(v_map_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object* v_n_1970_, lean_object* v_as_1971_, lean_object* v_lo_1972_, lean_object* v_hi_1973_, lean_object* v_w_1974_, lean_object* v_hlo_1975_, lean_object* v_hhi_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_n_1970_, v_as_1971_, v_lo_1972_, v_hi_1973_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object* v_n_1978_, lean_object* v_as_1979_, lean_object* v_lo_1980_, lean_object* v_hi_1981_, lean_object* v_w_1982_, lean_object* v_hlo_1983_, lean_object* v_hhi_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_n_1978_, v_as_1979_, v_lo_1980_, v_hi_1981_, v_w_1982_, v_hlo_1983_, v_hhi_1984_);
lean_dec(v_hi_1981_);
lean_dec(v_n_1978_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg(lean_object* v_map_1986_, lean_object* v_f_1987_, lean_object* v_init_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_1987_, v_map_1986_, v_init_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg___boxed(lean_object* v_map_1990_, lean_object* v_f_1991_, lean_object* v_init_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___redArg(v_map_1990_, v_f_1991_, v_init_1992_);
lean_dec_ref(v_map_1990_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(lean_object* v_00_u03c3_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_map_1996_, lean_object* v_f_1997_, lean_object* v_init_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_1997_, v_map_1996_, v_init_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7___boxed(lean_object* v_00_u03c3_2000_, lean_object* v_00_u03b2_2001_, lean_object* v_map_2002_, lean_object* v_f_2003_, lean_object* v_init_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7(v_00_u03c3_2000_, v_00_u03b2_2001_, v_map_2002_, v_f_2003_, v_init_2004_);
lean_dec_ref(v_map_2002_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(lean_object* v_n_2006_, lean_object* v_lo_2007_, lean_object* v_hi_2008_, lean_object* v_hhi_2009_, lean_object* v_pivot_2010_, lean_object* v_as_2011_, lean_object* v_i_2012_, lean_object* v_k_2013_, lean_object* v_ilo_2014_, lean_object* v_ik_2015_, lean_object* v_w_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___redArg(v_hi_2008_, v_pivot_2010_, v_as_2011_, v_i_2012_, v_k_2013_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11___boxed(lean_object* v_n_2018_, lean_object* v_lo_2019_, lean_object* v_hi_2020_, lean_object* v_hhi_2021_, lean_object* v_pivot_2022_, lean_object* v_as_2023_, lean_object* v_i_2024_, lean_object* v_k_2025_, lean_object* v_ilo_2026_, lean_object* v_ik_2027_, lean_object* v_w_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6_spec__11(v_n_2018_, v_lo_2019_, v_hi_2020_, v_hhi_2021_, v_pivot_2022_, v_as_2023_, v_i_2024_, v_k_2025_, v_ilo_2026_, v_ik_2027_, v_w_2028_);
lean_dec(v_pivot_2022_);
lean_dec(v_hi_2020_);
lean_dec(v_lo_2019_);
lean_dec(v_n_2018_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2030_, lean_object* v_constName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___redArg(v_constName_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_constName_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4(v_00_u03b1_2038_, v_constName_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10(lean_object* v_00_u03c3_2046_, lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_f_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___redArg(v_f_2049_, v_x_2050_, v_x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03c3_2053_, lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_f_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10(v_00_u03c3_2053_, v_00_u03b1_2054_, v_00_u03b2_2055_, v_f_2056_, v_x_2057_, v_x_2058_);
lean_dec_ref(v_x_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b1_2060_, lean_object* v_ref_2061_, lean_object* v_constName_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg(v_ref_2061_, v_constName_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_ref_2070_, lean_object* v_constName_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10(v_00_u03b1_2069_, v_ref_2070_, v_constName_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v_ref_2070_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_00_u03c3_2080_, lean_object* v_f_2081_, lean_object* v_as_2082_, size_t v_i_2083_, size_t v_stop_2084_, lean_object* v_b_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___redArg(v_f_2081_, v_as_2082_, v_i_2083_, v_stop_2084_, v_b_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_00_u03c3_2089_, lean_object* v_f_2090_, lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_){
_start:
{
size_t v_i_boxed_2095_; size_t v_stop_boxed_2096_; lean_object* v_res_2097_; 
v_i_boxed_2095_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2096_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__14(v_00_u03b1_2087_, v_00_u03b2_2088_, v_00_u03c3_2089_, v_f_2090_, v_as_2091_, v_i_boxed_2095_, v_stop_boxed_2096_, v_b_2094_);
lean_dec_ref(v_as_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15(lean_object* v_00_u03c3_2098_, lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_f_2101_, lean_object* v_keys_2102_, lean_object* v_vals_2103_, lean_object* v_heq_2104_, lean_object* v_i_2105_, lean_object* v_acc_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___redArg(v_f_2101_, v_keys_2102_, v_vals_2103_, v_i_2105_, v_acc_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03c3_2108_, lean_object* v_00_u03b1_2109_, lean_object* v_00_u03b2_2110_, lean_object* v_f_2111_, lean_object* v_keys_2112_, lean_object* v_vals_2113_, lean_object* v_heq_2114_, lean_object* v_i_2115_, lean_object* v_acc_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__7_spec__10_spec__15(v_00_u03c3_2108_, v_00_u03b1_2109_, v_00_u03b2_2110_, v_f_2111_, v_keys_2112_, v_vals_2113_, v_heq_2114_, v_i_2115_, v_acc_2116_);
lean_dec_ref(v_vals_2113_);
lean_dec_ref(v_keys_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15(lean_object* v_00_u03b1_2118_, lean_object* v_ref_2119_, lean_object* v_msg_2120_, lean_object* v_declHint_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___redArg(v_ref_2119_, v_msg_2120_, v_declHint_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_ref_2129_, lean_object* v_msg_2130_, lean_object* v_declHint_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15(v_00_u03b1_2128_, v_ref_2129_, v_msg_2130_, v_declHint_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_ref_2129_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20(lean_object* v_msg_2138_, lean_object* v_declHint_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___redArg(v_msg_2138_, v_declHint_2139_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20___boxed(lean_object* v_msg_2146_, lean_object* v_declHint_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__17_spec__20(v_msg_2146_, v_declHint_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18(lean_object* v_00_u03b1_2154_, lean_object* v_ref_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___redArg(v_ref_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_ref_2164_, lean_object* v_msg_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18(v_00_u03b1_2163_, v_ref_2164_, v_msg_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v_ref_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22(lean_object* v_00_u03b1_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22(v_00_u03b1_2180_, v_msg_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2187_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = l_Lean_Level_ofNat(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__1);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__2);
v___x_2196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__0));
v___x_2197_ = l_Lean_mkConst(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__2));
v___x_2200_ = l_Lean_mkConst(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_2203_ = l_Lean_mkConst(v___x_2202_, v___x_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object* v_tacticName_2204_, lean_object* v_expectedType_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v___x_2211_; 
lean_inc_ref(v_expectedType_2205_);
v___x_2211_ = l_Lean_Meta_mkDecide(v_expectedType_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; uint8_t v_transparency_2214_; lean_object* v___x_2215_; lean_object* v___y_2217_; uint8_t v___x_2250_; uint8_t v___x_2251_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = l_Lean_Meta_Context_config(v_a_2206_);
v_transparency_2214_ = lean_ctor_get_uint8(v___x_2213_, 9);
lean_dec_ref(v___x_2213_);
v___x_2215_ = l_Lean_Expr_appArg_x21(v_a_2212_);
v___x_2250_ = 1;
v___x_2251_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2214_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_inc(v_a_2209_);
lean_inc_ref(v_a_2208_);
lean_inc(v_a_2207_);
lean_inc_ref(v_a_2206_);
lean_inc(v_a_2212_);
v___x_2252_ = lean_whnf(v_a_2212_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
v___y_2217_ = v___x_2252_;
goto v___jp_2216_;
}
else
{
lean_object* v_keyedConfig_2253_; uint8_t v_trackZetaDelta_2254_; lean_object* v_zetaDeltaSet_2255_; lean_object* v_lctx_2256_; lean_object* v_localInstances_2257_; lean_object* v_defEqCtx_x3f_2258_; lean_object* v_synthPendingDepth_2259_; lean_object* v_customCanUnfoldPredicate_x3f_2260_; uint8_t v_univApprox_2261_; uint8_t v_inTypeClassResolution_2262_; uint8_t v_cacheInferType_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_keyedConfig_2253_ = lean_ctor_get(v_a_2206_, 0);
v_trackZetaDelta_2254_ = lean_ctor_get_uint8(v_a_2206_, sizeof(void*)*7);
v_zetaDeltaSet_2255_ = lean_ctor_get(v_a_2206_, 1);
v_lctx_2256_ = lean_ctor_get(v_a_2206_, 2);
v_localInstances_2257_ = lean_ctor_get(v_a_2206_, 3);
v_defEqCtx_x3f_2258_ = lean_ctor_get(v_a_2206_, 4);
v_synthPendingDepth_2259_ = lean_ctor_get(v_a_2206_, 5);
v_customCanUnfoldPredicate_x3f_2260_ = lean_ctor_get(v_a_2206_, 6);
v_univApprox_2261_ = lean_ctor_get_uint8(v_a_2206_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2262_ = lean_ctor_get_uint8(v_a_2206_, sizeof(void*)*7 + 2);
v_cacheInferType_2263_ = lean_ctor_get_uint8(v_a_2206_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2253_);
v___x_2264_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2250_, v_keyedConfig_2253_);
lean_inc(v_customCanUnfoldPredicate_x3f_2260_);
lean_inc(v_synthPendingDepth_2259_);
lean_inc(v_defEqCtx_x3f_2258_);
lean_inc_ref(v_localInstances_2257_);
lean_inc_ref(v_lctx_2256_);
lean_inc(v_zetaDeltaSet_2255_);
v___x_2265_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_zetaDeltaSet_2255_);
lean_ctor_set(v___x_2265_, 2, v_lctx_2256_);
lean_ctor_set(v___x_2265_, 3, v_localInstances_2257_);
lean_ctor_set(v___x_2265_, 4, v_defEqCtx_x3f_2258_);
lean_ctor_set(v___x_2265_, 5, v_synthPendingDepth_2259_);
lean_ctor_set(v___x_2265_, 6, v_customCanUnfoldPredicate_x3f_2260_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*7, v_trackZetaDelta_2254_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*7 + 1, v_univApprox_2261_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2262_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*7 + 3, v_cacheInferType_2263_);
lean_inc(v_a_2209_);
lean_inc_ref(v_a_2208_);
lean_inc(v_a_2207_);
lean_inc(v_a_2212_);
v___x_2266_ = lean_whnf(v_a_2212_, v___x_2265_, v_a_2207_, v_a_2208_, v_a_2209_);
v___y_2217_ = v___x_2266_;
goto v___jp_2216_;
}
v___jp_2216_:
{
if (lean_obj_tag(v___y_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2241_; 
v_a_2218_ = lean_ctor_get(v___y_2217_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___y_2217_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2220_ = v___y_2217_;
v_isShared_2221_ = v_isSharedCheck_2241_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___y_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2241_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_2223_ = l_Lean_Expr_isConstOf(v_a_2218_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_del_object(v___x_2220_);
lean_dec_ref(v___x_2215_);
lean_inc_ref(v_expectedType_2205_);
v___x_2224_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed), 9, 4);
lean_closure_set(v___x_2224_, 0, v_tacticName_2204_);
lean_closure_set(v___x_2224_, 1, v_expectedType_2205_);
lean_closure_set(v___x_2224_, 2, v_a_2212_);
lean_closure_set(v___x_2224_, 3, v_a_2218_);
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_mk_empty_array_with_capacity(v___x_2225_);
v___x_2227_ = lean_array_push(v___x_2226_, v_expectedType_2205_);
v___x_2228_ = l_Lean_MessageData_ofLazyM(v___x_2224_, v___x_2227_);
v___x_2229_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2228_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
lean_dec(v_a_2218_);
lean_dec(v_tacticName_2204_);
v___x_2230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__3);
v___x_2231_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__4);
v___x_2232_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___closed__5);
v___x_2233_ = l_Lean_mkApp3(v___x_2230_, v___x_2231_, v_a_2212_, v___x_2232_);
v___x_2234_ = l_Lean_reflBoolTrue;
v___x_2235_ = l_Lean_Meta_mkExpectedPropHint(v___x_2234_, v___x_2233_);
v___x_2236_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_2237_ = l_Lean_mkApp3(v___x_2236_, v_expectedType_2205_, v___x_2215_, v___x_2235_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2237_);
v___x_2239_ = v___x_2220_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2212_);
lean_dec_ref(v_expectedType_2205_);
lean_dec(v_tacticName_2204_);
v_a_2242_ = lean_ctor_get(v___y_2217_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___y_2217_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___y_2217_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___y_2217_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2205_);
lean_dec(v_tacticName_2204_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(lean_object* v_tacticName_2267_, lean_object* v_expectedType_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2267_, v_expectedType_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* v_tacticName_2275_, lean_object* v_expectedType_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2275_, v_expectedType_2276_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* v_tacticName_2287_, lean_object* v_expectedType_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(v_tacticName_2287_, v_expectedType_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object* v_a_2305_, lean_object* v_tacticName_2306_, lean_object* v_expectedType_2307_, lean_object* v___x_2308_, lean_object* v___x_2309_, uint8_t v___x_2310_, uint8_t v___x_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___y_2318_; lean_object* v_a_2319_; lean_object* v___y_2324_; lean_object* v___x_2358_; uint8_t v_transparency_2359_; uint8_t v___x_2360_; 
v___x_2358_ = l_Lean_Meta_Context_config(v___y_2312_);
v_transparency_2359_ = lean_ctor_get_uint8(v___x_2358_, 9);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2359_, v___x_2311_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc(v___y_2313_);
lean_inc_ref(v___y_2312_);
lean_inc_ref(v___x_2308_);
v___x_2361_ = lean_whnf(v___x_2308_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
v___y_2324_ = v___x_2361_;
goto v___jp_2323_;
}
else
{
lean_object* v_keyedConfig_2362_; uint8_t v_trackZetaDelta_2363_; lean_object* v_zetaDeltaSet_2364_; lean_object* v_lctx_2365_; lean_object* v_localInstances_2366_; lean_object* v_defEqCtx_x3f_2367_; lean_object* v_synthPendingDepth_2368_; lean_object* v_customCanUnfoldPredicate_x3f_2369_; uint8_t v_univApprox_2370_; uint8_t v_inTypeClassResolution_2371_; uint8_t v_cacheInferType_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_keyedConfig_2362_ = lean_ctor_get(v___y_2312_, 0);
v_trackZetaDelta_2363_ = lean_ctor_get_uint8(v___y_2312_, sizeof(void*)*7);
v_zetaDeltaSet_2364_ = lean_ctor_get(v___y_2312_, 1);
v_lctx_2365_ = lean_ctor_get(v___y_2312_, 2);
v_localInstances_2366_ = lean_ctor_get(v___y_2312_, 3);
v_defEqCtx_x3f_2367_ = lean_ctor_get(v___y_2312_, 4);
v_synthPendingDepth_2368_ = lean_ctor_get(v___y_2312_, 5);
v_customCanUnfoldPredicate_x3f_2369_ = lean_ctor_get(v___y_2312_, 6);
v_univApprox_2370_ = lean_ctor_get_uint8(v___y_2312_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2371_ = lean_ctor_get_uint8(v___y_2312_, sizeof(void*)*7 + 2);
v_cacheInferType_2372_ = lean_ctor_get_uint8(v___y_2312_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2362_);
v___x_2373_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2311_, v_keyedConfig_2362_);
lean_inc(v_customCanUnfoldPredicate_x3f_2369_);
lean_inc(v_synthPendingDepth_2368_);
lean_inc(v_defEqCtx_x3f_2367_);
lean_inc_ref(v_localInstances_2366_);
lean_inc_ref(v_lctx_2365_);
lean_inc(v_zetaDeltaSet_2364_);
v___x_2374_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_zetaDeltaSet_2364_);
lean_ctor_set(v___x_2374_, 2, v_lctx_2365_);
lean_ctor_set(v___x_2374_, 3, v_localInstances_2366_);
lean_ctor_set(v___x_2374_, 4, v_defEqCtx_x3f_2367_);
lean_ctor_set(v___x_2374_, 5, v_synthPendingDepth_2368_);
lean_ctor_set(v___x_2374_, 6, v_customCanUnfoldPredicate_x3f_2369_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*7, v_trackZetaDelta_2363_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*7 + 1, v_univApprox_2370_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2371_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*7 + 3, v_cacheInferType_2372_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc(v___y_2313_);
lean_inc_ref(v___x_2308_);
v___x_2375_ = lean_whnf(v___x_2308_, v___x_2374_, v___y_2313_, v___y_2314_, v___y_2315_);
v___y_2324_ = v___x_2375_;
goto v___jp_2323_;
}
v___jp_2317_:
{
uint8_t v___x_2320_; 
v___x_2320_ = l_Lean_Exception_isInterrupt(v_a_2319_);
lean_dec_ref(v_a_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec_ref(v___y_2318_);
v___x_2321_ = l_Lean_Exception_toMessageData(v_a_2305_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
else
{
lean_dec_ref(v_a_2305_);
return v___y_2318_;
}
}
v___jp_2323_:
{
if (lean_obj_tag(v___y_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2349_; 
v_a_2325_ = lean_ctor_get(v___y_2324_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___y_2324_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2327_ = v___y_2324_;
v_isShared_2328_ = v_isSharedCheck_2349_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___y_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2349_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__6));
v___x_2330_ = l_Lean_Expr_isConstOf(v_a_2325_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
lean_del_object(v___x_2327_);
lean_dec_ref(v___x_2309_);
v___x_2331_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_2306_, v_expectedType_2307_, v___x_2308_, v_a_2325_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec_ref(v___y_2312_);
lean_dec(v_a_2325_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_dec_ref(v_a_2305_);
return v___x_2331_;
}
else
{
lean_object* v_a_2332_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
v___y_2318_ = v___x_2331_;
v_a_2319_ = v_a_2332_;
goto v___jp_2317_;
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec(v_a_2325_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___x_2308_);
lean_dec_ref(v_expectedType_2307_);
v___x_2333_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2334_ = l_Lean_MessageData_ofName(v_tacticName_2306_);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = l_Lean_Name_mkStr1(v___x_2309_);
v___x_2339_ = l_Lean_MessageData_ofConstName(v___x_2338_, v___x_2310_);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2337_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_Exception_toMessageData(v_a_2305_);
v___x_2344_ = l_Lean_indentD(v___x_2343_);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2342_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2345_);
v___x_2347_ = v___x_2327_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___x_2309_);
lean_dec_ref(v___x_2308_);
lean_dec_ref(v_expectedType_2307_);
lean_dec(v_tacticName_2306_);
v_a_2350_ = lean_ctor_get(v___y_2324_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___y_2324_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___y_2324_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___y_2324_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
lean_inc(v_a_2350_);
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
v___y_2318_ = v___x_2355_;
v_a_2319_ = v_a_2350_;
goto v___jp_2317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object* v_a_2376_, lean_object* v_tacticName_2377_, lean_object* v_expectedType_2378_, lean_object* v___x_2379_, lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v___x_6416__boxed_2388_; uint8_t v___x_6417__boxed_2389_; lean_object* v_res_2390_; 
v___x_6416__boxed_2388_ = lean_unbox(v___x_2381_);
v___x_6417__boxed_2389_ = lean_unbox(v___x_2382_);
v_res_2390_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(v_a_2376_, v_tacticName_2377_, v_expectedType_2378_, v___x_2379_, v___x_2380_, v___x_6416__boxed_2388_, v___x_6417__boxed_2389_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
return v_res_2390_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(lean_object* v_a_2391_, lean_object* v_as_2392_, size_t v_i_2393_, size_t v_stop_2394_){
_start:
{
uint8_t v___x_2395_; 
v___x_2395_ = lean_usize_dec_eq(v_i_2393_, v_stop_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_array_uget_borrowed(v_as_2392_, v_i_2393_);
v___x_2397_ = lean_name_eq(v_a_2391_, v___x_2396_);
if (v___x_2397_ == 0)
{
size_t v___x_2398_; size_t v___x_2399_; 
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2393_, v___x_2398_);
v_i_2393_ = v___x_2399_;
goto _start;
}
else
{
return v___x_2397_;
}
}
else
{
uint8_t v___x_2401_; 
v___x_2401_ = 0;
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(lean_object* v_a_2402_, lean_object* v_as_2403_, lean_object* v_i_2404_, lean_object* v_stop_2405_){
_start:
{
size_t v_i_boxed_2406_; size_t v_stop_boxed_2407_; uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_i_boxed_2406_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_stop_boxed_2407_ = lean_unbox_usize(v_stop_2405_);
lean_dec(v_stop_2405_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2402_, v_as_2403_, v_i_boxed_2406_, v_stop_boxed_2407_);
lean_dec_ref(v_as_2403_);
lean_dec(v_a_2402_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object* v_as_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = lean_array_get_size(v_as_2410_);
v___x_2414_ = lean_nat_dec_lt(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
return v___x_2414_;
}
else
{
if (v___x_2414_ == 0)
{
return v___x_2414_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2413_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2411_, v_as_2410_, v___x_2415_, v___x_2416_);
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object* v_as_2418_, lean_object* v_a_2419_){
_start:
{
uint8_t v_res_2420_; lean_object* v_r_2421_; 
v_res_2420_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v_as_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_as_2418_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(lean_object* v___x_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
if (lean_obj_tag(v_a_2423_) == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = l_List_reverse___redArg(v_a_2424_);
return v___x_2425_;
}
else
{
lean_object* v_head_2426_; lean_object* v_tail_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2437_; 
v_head_2426_ = lean_ctor_get(v_a_2423_, 0);
v_tail_2427_ = lean_ctor_get(v_a_2423_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_a_2423_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2429_ = v_a_2423_;
v_isShared_2430_ = v_isSharedCheck_2437_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_tail_2427_);
lean_inc(v_head_2426_);
lean_dec(v_a_2423_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2437_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
uint8_t v___x_2431_; 
v___x_2431_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v___x_2422_, v_head_2426_);
if (v___x_2431_ == 0)
{
lean_del_object(v___x_2429_);
lean_dec(v_head_2426_);
v_a_2423_ = v_tail_2427_;
goto _start;
}
else
{
lean_object* v___x_2434_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v_a_2424_);
v___x_2434_ = v___x_2429_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_head_2426_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_a_2424_);
v___x_2434_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
v_a_2423_ = v_tail_2427_;
v_a_2424_ = v___x_2434_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(lean_object* v___x_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v___x_2438_, v_a_2439_, v_a_2440_);
lean_dec_ref(v___x_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
if (lean_obj_tag(v_a_2442_) == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = l_List_reverse___redArg(v_a_2443_);
return v___x_2444_;
}
else
{
lean_object* v_head_2445_; lean_object* v_tail_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
v_head_2445_ = lean_ctor_get(v_a_2442_, 0);
v_tail_2446_ = lean_ctor_get(v_a_2442_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_a_2442_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v_a_2442_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_tail_2446_);
lean_inc(v_head_2445_);
lean_dec(v_a_2442_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = l_Lean_Level_param___override(v_head_2445_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v_a_2443_);
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2452_ = v___x_2448_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_a_2443_);
v___x_2452_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
v_a_2442_ = v_tail_2446_;
v_a_2443_ = v___x_2452_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_unsigned_to_nat(16u);
v___x_2458_ = lean_mk_array(v___x_2457_, v___x_2456_);
return v___x_2458_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
return v___x_2461_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2463_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1);
v___x_2464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
lean_ctor_set(v___x_2464_, 2, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_box(0);
v___x_2470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__4));
v___x_2471_ = l_Lean_mkConst(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object* v_tacticName_2472_, lean_object* v_expectedType_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; 
lean_inc_ref(v_expectedType_2473_);
v___x_2482_ = l_Lean_Meta_mkDecideProof(v_expectedType_2473_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = l_Lean_Elab_Term_getLevelNames___redArg(v_a_2476_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2486_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2486_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_2474_, v_a_2476_, v_a_2478_, v_a_2480_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2606_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2606_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2606_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_toCold_2494_; lean_object* v_params_2495_; lean_object* v_currRecDepth_2496_; lean_object* v_ref_2497_; uint8_t v_suppressElabErrors_2498_; lean_object* v_fileName_2499_; lean_object* v_fileMap_2500_; lean_object* v_options_2501_; lean_object* v_currNamespace_2502_; lean_object* v_openDecls_2503_; lean_object* v_initHeartbeats_2504_; lean_object* v_maxHeartbeats_2505_; lean_object* v_quotContext_2506_; lean_object* v_currMacroScope_2507_; lean_object* v_cancelTk_x3f_2508_; lean_object* v_inheritedTraceOptions_2509_; lean_object* v_env_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; uint8_t v___x_2518_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v_fileName_2551_; lean_object* v_fileMap_2552_; lean_object* v_currNamespace_2553_; lean_object* v_openDecls_2554_; lean_object* v_initHeartbeats_2555_; lean_object* v_maxHeartbeats_2556_; lean_object* v_quotContext_2557_; lean_object* v_currMacroScope_2558_; lean_object* v_cancelTk_x3f_2559_; lean_object* v_inheritedTraceOptions_2560_; lean_object* v_currRecDepth_2561_; lean_object* v_ref_2562_; uint8_t v_suppressElabErrors_2563_; lean_object* v___y_2564_; uint8_t v___y_2584_; uint8_t v___x_2605_; 
v___x_2491_ = lean_st_ref_get(v_a_2480_);
v___x_2492_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2);
lean_inc_ref(v_expectedType_2473_);
v___x_2493_ = l_Lean_collectLevelParams(v___x_2492_, v_expectedType_2473_);
v_toCold_2494_ = lean_ctor_get(v_a_2479_, 0);
v_params_2495_ = lean_ctor_get(v___x_2493_, 2);
lean_inc_ref(v_params_2495_);
lean_dec_ref(v___x_2493_);
v_currRecDepth_2496_ = lean_ctor_get(v_a_2479_, 1);
v_ref_2497_ = lean_ctor_get(v_a_2479_, 2);
v_suppressElabErrors_2498_ = lean_ctor_get_uint8(v_a_2479_, sizeof(void*)*3 + 1);
v_fileName_2499_ = lean_ctor_get(v_toCold_2494_, 0);
v_fileMap_2500_ = lean_ctor_get(v_toCold_2494_, 1);
v_options_2501_ = lean_ctor_get(v_toCold_2494_, 2);
v_currNamespace_2502_ = lean_ctor_get(v_toCold_2494_, 4);
v_openDecls_2503_ = lean_ctor_get(v_toCold_2494_, 5);
v_initHeartbeats_2504_ = lean_ctor_get(v_toCold_2494_, 6);
v_maxHeartbeats_2505_ = lean_ctor_get(v_toCold_2494_, 7);
v_quotContext_2506_ = lean_ctor_get(v_toCold_2494_, 8);
v_currMacroScope_2507_ = lean_ctor_get(v_toCold_2494_, 9);
v_cancelTk_x3f_2508_ = lean_ctor_get(v_toCold_2494_, 10);
v_inheritedTraceOptions_2509_ = lean_ctor_get(v_toCold_2494_, 11);
v_env_2510_ = lean_ctor_get(v___x_2491_, 0);
lean_inc_ref(v_env_2510_);
lean_dec(v___x_2491_);
v___x_2511_ = l_Lean_Expr_appFn_x21(v_a_2483_);
v___x_2512_ = l_Lean_Expr_appArg_x21(v___x_2511_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = l_List_reverse___redArg(v_a_2485_);
v___x_2514_ = lean_box(0);
v___x_2515_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v_params_2495_, v___x_2513_, v___x_2514_);
lean_dec_ref(v_params_2495_);
v___x_2516_ = lean_box(0);
v___x_2517_ = 1;
v___x_2518_ = 0;
v___x_2546_ = l_Lean_Elab_async;
lean_inc_ref(v_options_2501_);
v___x_2547_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_options_2501_, v___x_2546_, v___x_2518_);
v___x_2548_ = l_Lean_diagnostics;
v___x_2549_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_2547_, v___x_2548_);
v___x_2605_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2510_);
lean_dec_ref(v_env_2510_);
if (v___x_2549_ == 0)
{
if (v___x_2605_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_2509_);
lean_inc(v_cancelTk_x3f_2508_);
lean_inc(v_currMacroScope_2507_);
lean_inc(v_quotContext_2506_);
lean_inc(v_maxHeartbeats_2505_);
lean_inc(v_initHeartbeats_2504_);
lean_inc(v_openDecls_2503_);
lean_inc(v_currNamespace_2502_);
lean_inc_ref(v_fileMap_2500_);
lean_inc_ref(v_fileName_2499_);
v_fileName_2551_ = v_fileName_2499_;
v_fileMap_2552_ = v_fileMap_2500_;
v_currNamespace_2553_ = v_currNamespace_2502_;
v_openDecls_2554_ = v_openDecls_2503_;
v_initHeartbeats_2555_ = v_initHeartbeats_2504_;
v_maxHeartbeats_2556_ = v_maxHeartbeats_2505_;
v_quotContext_2557_ = v_quotContext_2506_;
v_currMacroScope_2558_ = v_currMacroScope_2507_;
v_cancelTk_x3f_2559_ = v_cancelTk_x3f_2508_;
v_inheritedTraceOptions_2560_ = v_inheritedTraceOptions_2509_;
v_currRecDepth_2561_ = v_currRecDepth_2496_;
v_ref_2562_ = v_ref_2497_;
v_suppressElabErrors_2563_ = v_suppressElabErrors_2498_;
v___y_2564_ = v_a_2480_;
goto v___jp_2550_;
}
else
{
v___y_2584_ = v___x_2549_;
goto v___jp_2583_;
}
}
else
{
v___y_2584_ = v___x_2605_;
goto v___jp_2583_;
}
v___jp_2519_:
{
if (v___y_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_del_object(v___x_2489_);
v___x_2522_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2487_, v___y_2521_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec_ref_known(v___x_2522_, 1);
v___x_2523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___redArg___closed__3));
v___x_2524_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__5);
lean_inc_ref_n(v_expectedType_2473_, 2);
v___x_2525_ = l_Lean_mkAppB(v___x_2524_, v_expectedType_2473_, v___x_2512_);
v___x_2526_ = 1;
v___x_2527_ = lean_box(v___x_2518_);
v___x_2528_ = lean_box(v___x_2526_);
v___f_2529_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_2529_, 0, v___y_2520_);
lean_closure_set(v___f_2529_, 1, v_tacticName_2472_);
lean_closure_set(v___f_2529_, 2, v_expectedType_2473_);
lean_closure_set(v___f_2529_, 3, v___x_2525_);
lean_closure_set(v___f_2529_, 4, v___x_2523_);
lean_closure_set(v___f_2529_, 5, v___x_2527_);
lean_closure_set(v___f_2529_, 6, v___x_2528_);
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = lean_mk_empty_array_with_capacity(v___x_2530_);
v___x_2532_ = lean_array_push(v___x_2531_, v_expectedType_2473_);
v___x_2533_ = l_Lean_MessageData_ofLazyM(v___f_2529_, v___x_2532_);
v___x_2534_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2533_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___x_2512_);
lean_dec_ref(v_expectedType_2473_);
lean_dec(v_tacticName_2472_);
v_a_2535_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2522_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2522_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v___x_2544_; 
lean_dec_ref(v___x_2512_);
lean_dec(v_a_2487_);
lean_dec_ref(v_expectedType_2473_);
lean_dec(v_tacticName_2472_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 1);
lean_ctor_set(v___x_2489_, 0, v___y_2520_);
v___x_2544_ = v___x_2489_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___y_2520_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
v___jp_2550_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2565_ = l_Lean_maxRecDepth;
v___x_2566_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v___x_2547_, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2567_, 0, v_fileName_2551_);
lean_ctor_set(v___x_2567_, 1, v_fileMap_2552_);
lean_ctor_set(v___x_2567_, 2, v___x_2547_);
lean_ctor_set(v___x_2567_, 3, v___x_2566_);
lean_ctor_set(v___x_2567_, 4, v_currNamespace_2553_);
lean_ctor_set(v___x_2567_, 5, v_openDecls_2554_);
lean_ctor_set(v___x_2567_, 6, v_initHeartbeats_2555_);
lean_ctor_set(v___x_2567_, 7, v_maxHeartbeats_2556_);
lean_ctor_set(v___x_2567_, 8, v_quotContext_2557_);
lean_ctor_set(v___x_2567_, 9, v_currMacroScope_2558_);
lean_ctor_set(v___x_2567_, 10, v_cancelTk_x3f_2559_);
lean_ctor_set(v___x_2567_, 11, v_inheritedTraceOptions_2560_);
lean_inc(v_ref_2562_);
lean_inc(v_currRecDepth_2561_);
v___x_2568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v_currRecDepth_2561_);
lean_ctor_set(v___x_2568_, 2, v_ref_2562_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*3, v___x_2549_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*3 + 1, v_suppressElabErrors_2563_);
lean_inc_ref(v_expectedType_2473_);
lean_inc(v___x_2515_);
v___x_2569_ = l_Lean_Meta_mkAuxLemma(v___x_2515_, v_expectedType_2473_, v_a_2483_, v___x_2516_, v___x_2517_, v___x_2518_, v___x_2518_, v___x_2518_, v_a_2477_, v_a_2478_, v___x_2568_, v___y_2564_);
lean_dec_ref_known(v___x_2568_, 3);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v___x_2512_);
lean_del_object(v___x_2489_);
lean_dec(v_a_2487_);
lean_dec_ref(v_expectedType_2473_);
lean_dec(v_tacticName_2472_);
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(v___x_2515_, v___x_2514_);
v___x_2575_ = l_Lean_mkConst(v_a_2570_, v___x_2574_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v_a_2580_; uint8_t v___x_2581_; 
lean_dec(v___x_2515_);
v_a_2580_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2581_ = l_Lean_Exception_isInterrupt(v_a_2580_);
if (v___x_2581_ == 0)
{
uint8_t v___x_2582_; 
lean_inc(v_a_2580_);
v___x_2582_ = l_Lean_Exception_isRuntime(v_a_2580_);
v___y_2520_ = v_a_2580_;
v___y_2521_ = v___x_2582_;
goto v___jp_2519_;
}
else
{
v___y_2520_ = v_a_2580_;
v___y_2521_ = v___x_2581_;
goto v___jp_2519_;
}
}
}
v___jp_2583_:
{
if (v___y_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v_env_2586_; lean_object* v_nextMacroScope_2587_; lean_object* v_ngen_2588_; lean_object* v_auxDeclNGen_2589_; lean_object* v_traceState_2590_; lean_object* v_messages_2591_; lean_object* v_infoState_2592_; lean_object* v_snapshotTasks_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2603_; 
v___x_2585_ = lean_st_ref_take(v_a_2480_);
v_env_2586_ = lean_ctor_get(v___x_2585_, 0);
v_nextMacroScope_2587_ = lean_ctor_get(v___x_2585_, 1);
v_ngen_2588_ = lean_ctor_get(v___x_2585_, 2);
v_auxDeclNGen_2589_ = lean_ctor_get(v___x_2585_, 3);
v_traceState_2590_ = lean_ctor_get(v___x_2585_, 4);
v_messages_2591_ = lean_ctor_get(v___x_2585_, 6);
v_infoState_2592_ = lean_ctor_get(v___x_2585_, 7);
v_snapshotTasks_2593_ = lean_ctor_get(v___x_2585_, 8);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2585_, 5);
lean_dec(v_unused_2604_);
v___x_2595_ = v___x_2585_;
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snapshotTasks_2593_);
lean_inc(v_infoState_2592_);
lean_inc(v_messages_2591_);
lean_inc(v_traceState_2590_);
lean_inc(v_auxDeclNGen_2589_);
lean_inc(v_ngen_2588_);
lean_inc(v_nextMacroScope_2587_);
lean_inc(v_env_2586_);
lean_dec(v___x_2585_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = l_Lean_Kernel_enableDiag(v_env_2586_, v___x_2549_);
v___x_2598_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 5, v___x_2598_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_nextMacroScope_2587_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_ngen_2588_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_auxDeclNGen_2589_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_traceState_2590_);
lean_ctor_set(v_reuseFailAlloc_2602_, 5, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2602_, 6, v_messages_2591_);
lean_ctor_set(v_reuseFailAlloc_2602_, 7, v_infoState_2592_);
lean_ctor_set(v_reuseFailAlloc_2602_, 8, v_snapshotTasks_2593_);
v___x_2600_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_st_ref_put(v_a_2480_, v___x_2600_);
lean_inc_ref(v_inheritedTraceOptions_2509_);
lean_inc(v_cancelTk_x3f_2508_);
lean_inc(v_currMacroScope_2507_);
lean_inc(v_quotContext_2506_);
lean_inc(v_maxHeartbeats_2505_);
lean_inc(v_initHeartbeats_2504_);
lean_inc(v_openDecls_2503_);
lean_inc(v_currNamespace_2502_);
lean_inc_ref(v_fileMap_2500_);
lean_inc_ref(v_fileName_2499_);
v_fileName_2551_ = v_fileName_2499_;
v_fileMap_2552_ = v_fileMap_2500_;
v_currNamespace_2553_ = v_currNamespace_2502_;
v_openDecls_2554_ = v_openDecls_2503_;
v_initHeartbeats_2555_ = v_initHeartbeats_2504_;
v_maxHeartbeats_2556_ = v_maxHeartbeats_2505_;
v_quotContext_2557_ = v_quotContext_2506_;
v_currMacroScope_2558_ = v_currMacroScope_2507_;
v_cancelTk_x3f_2559_ = v_cancelTk_x3f_2508_;
v_inheritedTraceOptions_2560_ = v_inheritedTraceOptions_2509_;
v_currRecDepth_2561_ = v_currRecDepth_2496_;
v_ref_2562_ = v_ref_2497_;
v_suppressElabErrors_2563_ = v_suppressElabErrors_2498_;
v___y_2564_ = v_a_2480_;
goto v___jp_2550_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_2509_);
lean_inc(v_cancelTk_x3f_2508_);
lean_inc(v_currMacroScope_2507_);
lean_inc(v_quotContext_2506_);
lean_inc(v_maxHeartbeats_2505_);
lean_inc(v_initHeartbeats_2504_);
lean_inc(v_openDecls_2503_);
lean_inc(v_currNamespace_2502_);
lean_inc_ref(v_fileMap_2500_);
lean_inc_ref(v_fileName_2499_);
v_fileName_2551_ = v_fileName_2499_;
v_fileMap_2552_ = v_fileMap_2500_;
v_currNamespace_2553_ = v_currNamespace_2502_;
v_openDecls_2554_ = v_openDecls_2503_;
v_initHeartbeats_2555_ = v_initHeartbeats_2504_;
v_maxHeartbeats_2556_ = v_maxHeartbeats_2505_;
v_quotContext_2557_ = v_quotContext_2506_;
v_currMacroScope_2558_ = v_currMacroScope_2507_;
v_cancelTk_x3f_2559_ = v_cancelTk_x3f_2508_;
v_inheritedTraceOptions_2560_ = v_inheritedTraceOptions_2509_;
v_currRecDepth_2561_ = v_currRecDepth_2496_;
v_ref_2562_ = v_ref_2497_;
v_suppressElabErrors_2563_ = v_suppressElabErrors_2498_;
v___y_2564_ = v_a_2480_;
goto v___jp_2550_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_a_2485_);
lean_dec(v_a_2483_);
lean_dec_ref(v_expectedType_2473_);
lean_dec(v_tacticName_2472_);
v_a_2607_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2486_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2486_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v_a_2483_);
lean_dec_ref(v_expectedType_2473_);
lean_dec(v_tacticName_2472_);
v_a_2615_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2484_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2484_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2473_);
lean_dec(v_tacticName_2472_);
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object* v_tacticName_2623_, lean_object* v_expectedType_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2623_, v_expectedType_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* v_tacticName_2634_, lean_object* v_expectedType_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2634_, v_expectedType_2635_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* v_tacticName_2646_, lean_object* v_expectedType_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(v_tacticName_2646_, v_expectedType_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
return v_res_2657_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0));
v___x_2660_ = l_Lean_stringToMessageData(v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t v_native_2661_, uint8_t v_kernel_2662_, lean_object* v_tacticName_2663_, lean_object* v_expectedType_2664_, lean_object* v_x_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; 
if (v_kernel_2662_ == 0)
{
v___y_2676_ = v___y_2666_;
v___y_2677_ = v___y_2667_;
v___y_2678_ = v___y_2668_;
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
v___y_2683_ = v___y_2673_;
goto v___jp_2675_;
}
else
{
if (v_native_2661_ == 0)
{
v___y_2676_ = v___y_2666_;
v___y_2677_ = v___y_2667_;
v___y_2678_ = v___y_2668_;
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
v___y_2683_ = v___y_2673_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_expectedType_2664_);
v___x_2691_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2692_ = l_Lean_MessageData_ofName(v_tacticName_2663_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_obj_once(&l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1, &l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2695_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
v___jp_2675_:
{
lean_object* v___x_2684_; 
v___x_2684_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_2664_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2684_) == 0)
{
if (v_native_2661_ == 0)
{
if (v_kernel_2662_ == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2686_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2663_, v_a_2685_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2686_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2688_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2663_, v_a_2687_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2688_;
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2690_; 
v_a_2689_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2690_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_2663_, v_a_2689_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2690_;
}
}
else
{
lean_dec(v_tacticName_2663_);
return v___x_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object* v_native_2705_, lean_object* v_kernel_2706_, lean_object* v_tacticName_2707_, lean_object* v_expectedType_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v_native_boxed_2719_; uint8_t v_kernel_boxed_2720_; lean_object* v_res_2721_; 
v_native_boxed_2719_ = lean_unbox(v_native_2705_);
v_kernel_boxed_2720_ = lean_unbox(v_kernel_2706_);
v_res_2721_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0(v_native_boxed_2719_, v_kernel_boxed_2720_, v_tacticName_2707_, v_expectedType_2708_, v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v_x_2709_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t v_revert_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2724_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2735_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_a_2733_, v___x_2734_, v_revert_2722_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_n(v_a_2736_, 2);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Lean_MVarId_getDecl(v_a_2736_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v_lctx_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v_lctx_2739_ = lean_ctor_get(v_a_2738_, 1);
lean_inc_ref(v_lctx_2739_);
lean_dec(v_a_2738_);
v___x_2740_ = l_Lean_LocalContext_getFVarIds(v_lctx_2739_);
lean_dec_ref(v_lctx_2739_);
v___x_2741_ = 0;
v___x_2742_ = l_Lean_MVarId_revert(v_a_2736_, v___x_2740_, v___x_2741_, v_revert_2722_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v_snd_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2753_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v_snd_2744_ = lean_ctor_get(v_a_2743_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v_a_2743_, 0);
lean_dec(v_unused_2754_);
v___x_2746_ = v_a_2743_;
v_isShared_2747_ = v_isSharedCheck_2753_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snd_2744_);
lean_dec(v_a_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2753_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_box(0);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 1);
lean_ctor_set(v___x_2746_, 1, v___x_2748_);
lean_ctor_set(v___x_2746_, 0, v_snd_2744_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_snd_2744_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2750_, v___y_2724_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v___x_2751_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2742_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2742_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
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
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2736_);
v_a_2763_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2737_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2737_);
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
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_a_2771_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2735_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2735_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_a_2779_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2732_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2732_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object* v_revert_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
uint8_t v_revert_boxed_2797_; lean_object* v_res_2798_; 
v_revert_boxed_2797_ = lean_unbox(v_revert_2787_);
v_res_2798_ = l_Lean_Elab_Tactic_evalDecideCore___lam__1(v_revert_boxed_2797_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* v_tacticName_2799_, lean_object* v_cfg_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v_kernel_2810_; uint8_t v_native_2811_; uint8_t v_revert_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___f_2815_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; 
v_kernel_2810_ = lean_ctor_get_uint8(v_cfg_2800_, 0);
v_native_2811_ = lean_ctor_get_uint8(v_cfg_2800_, 1);
v_revert_2812_ = lean_ctor_get_uint8(v_cfg_2800_, 3);
v___x_2813_ = lean_box(v_native_2811_);
v___x_2814_ = lean_box(v_kernel_2810_);
lean_inc(v_tacticName_2799_);
v___f_2815_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2815_, 0, v___x_2813_);
lean_closure_set(v___f_2815_, 1, v___x_2814_);
lean_closure_set(v___f_2815_, 2, v_tacticName_2799_);
if (v_revert_2812_ == 0)
{
v___y_2817_ = v_a_2801_;
v___y_2818_ = v_a_2802_;
v___y_2819_ = v_a_2803_;
v___y_2820_ = v_a_2804_;
v___y_2821_ = v_a_2805_;
v___y_2822_ = v_a_2806_;
v___y_2823_ = v_a_2807_;
v___y_2824_ = v_a_2808_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2827_; lean_object* v___f_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_box(v_revert_2812_);
v___f_2828_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2828_, 0, v___x_2827_);
v___x_2829_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2828_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_dec_ref_known(v___x_2829_, 1);
v___y_2817_ = v_a_2801_;
v___y_2818_ = v_a_2802_;
v___y_2819_ = v_a_2803_;
v___y_2820_ = v_a_2804_;
v___y_2821_ = v_a_2805_;
v___y_2822_ = v_a_2806_;
v___y_2823_ = v_a_2807_;
v___y_2824_ = v_a_2808_;
goto v___jp_2816_;
}
else
{
lean_dec_ref(v___f_2815_);
lean_dec(v_tacticName_2799_);
return v___x_2829_;
}
}
v___jp_2816_:
{
uint8_t v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = 1;
v___x_2826_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacticName_2799_, v___f_2815_, v___x_2825_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object* v_tacticName_2830_, lean_object* v_cfg_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Elab_Tactic_evalDecideCore(v_tacticName_2830_, v_cfg_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec_ref(v_cfg_2831_);
return v_res_2841_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = lean_box(0);
v___x_2843_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(lean_object* v_00_u03b1_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(v_00_u03b1_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
return v_res_2863_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1));
v___x_2867_ = l_Lean_stringToMessageData(v___x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(lean_object* v___x_2868_, lean_object* v_ctor_2869_, lean_object* v_args_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0));
v___x_2938_ = lean_string_dec_eq(v_ctor_2869_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = lean_array_get_size(v_args_2870_);
v___x_2941_ = lean_unsigned_to_nat(4u);
v___x_2942_ = lean_nat_dec_eq(v___x_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v___x_2943_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2);
v___x_2944_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10_spec__15_spec__18_spec__22___redArg(v___x_2943_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
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
else
{
goto v___jp_2876_;
}
}
v___jp_2876_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_unsigned_to_nat(0u);
v___x_2878_ = lean_array_get_borrowed(v___x_2868_, v_args_2870_, v___x_2877_);
lean_inc(v___x_2878_);
v___x_2879_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2878_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = lean_array_get_borrowed(v___x_2868_, v_args_2870_, v___x_2881_);
lean_inc(v___x_2882_);
v___x_2883_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2882_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = lean_unsigned_to_nat(2u);
v___x_2886_ = lean_array_get_borrowed(v___x_2868_, v_args_2870_, v___x_2885_);
lean_inc(v___x_2886_);
v___x_2887_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2886_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = lean_unsigned_to_nat(3u);
v___x_2890_ = lean_array_get_borrowed(v___x_2868_, v_args_2870_, v___x_2889_);
lean_inc(v___x_2890_);
v___x_2891_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_2890_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2904_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; uint8_t v___x_2898_; uint8_t v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2902_; 
v___x_2896_ = lean_alloc_ctor(0, 0, 4);
v___x_2897_ = lean_unbox(v_a_2880_);
lean_dec(v_a_2880_);
lean_ctor_set_uint8(v___x_2896_, 0, v___x_2897_);
v___x_2898_ = lean_unbox(v_a_2884_);
lean_dec(v_a_2884_);
lean_ctor_set_uint8(v___x_2896_, 1, v___x_2898_);
v___x_2899_ = lean_unbox(v_a_2888_);
lean_dec(v_a_2888_);
lean_ctor_set_uint8(v___x_2896_, 2, v___x_2899_);
v___x_2900_ = lean_unbox(v_a_2892_);
lean_dec(v_a_2892_);
lean_ctor_set_uint8(v___x_2896_, 3, v___x_2900_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2902_ = v___x_2894_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2896_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_a_2888_);
lean_dec(v_a_2884_);
lean_dec(v_a_2880_);
v_a_2905_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2891_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2891_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_a_2884_);
lean_dec(v_a_2880_);
v_a_2913_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2887_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2887_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_a_2880_);
v_a_2921_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2883_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2883_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
v_a_2929_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2879_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2879_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed(lean_object* v___x_2953_, lean_object* v_ctor_2954_, lean_object* v_args_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(v___x_2953_, v_ctor_2954_, v_args_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v_args_2955_);
lean_dec_ref(v_ctor_2954_);
lean_dec_ref(v___x_2953_);
return v_res_2961_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___f_2963_; 
v___x_2962_ = l_Lean_instInhabitedExpr;
v___f_2963_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2963_, 0, v___x_2962_);
return v___f_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___f_2979_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0);
v___x_2980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_2981_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_2980_, v___f_2979_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed(lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
return v_res_2988_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_2992_ = l_Lean_Expr_const___override(v___x_2991_, v___x_2990_);
return v___x_2992_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
v___x_2996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0));
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v___x_2995_);
return v___x_2997_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig(void){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3);
return v___x_2998_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_box(0);
v___x_3000_ = l_Lean_Elab_abortTermExceptionId;
v___x_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
return v_res_3006_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0));
v___x_3009_ = l_Lean_stringToMessageData(v___x_3008_);
return v___x_3009_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
v___x_3011_ = l_Lean_MessageData_ofExpr(v___x_3010_);
return v___x_3011_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2);
v___x_3013_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0_spec__4_spec__10___redArg___closed__3);
v___x_3016_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5));
v___x_3020_ = l_Lean_stringToMessageData(v___x_3019_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7));
v___x_3023_ = l_Lean_stringToMessageData(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_ty_x3f_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_toCold_3038_; lean_object* v_currRecDepth_3039_; lean_object* v_ref_3040_; uint8_t v_diag_3041_; uint8_t v_suppressElabErrors_3042_; uint8_t v___x_3043_; lean_object* v_ref_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_ty_x3f_3032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
v___x_3033_ = 1;
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_box(v___x_3033_);
v___x_3036_ = lean_box(v___x_3033_);
lean_inc(v_stx_3024_);
v___x_3037_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_3037_, 0, v_stx_3024_);
lean_closure_set(v___x_3037_, 1, v_ty_x3f_3032_);
lean_closure_set(v___x_3037_, 2, v___x_3035_);
lean_closure_set(v___x_3037_, 3, v___x_3036_);
lean_closure_set(v___x_3037_, 4, v___x_3034_);
v_toCold_3038_ = lean_ctor_get(v_a_3029_, 0);
v_currRecDepth_3039_ = lean_ctor_get(v_a_3029_, 1);
v_ref_3040_ = lean_ctor_get(v_a_3029_, 2);
v_diag_3041_ = lean_ctor_get_uint8(v_a_3029_, sizeof(void*)*3);
v_suppressElabErrors_3042_ = lean_ctor_get_uint8(v_a_3029_, sizeof(void*)*3 + 1);
v___x_3043_ = 1;
v_ref_3044_ = l_Lean_replaceRef(v_stx_3024_, v_ref_3040_);
lean_dec(v_stx_3024_);
lean_inc(v_currRecDepth_3039_);
lean_inc_ref(v_toCold_3038_);
v___x_3045_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3045_, 0, v_toCold_3038_);
lean_ctor_set(v___x_3045_, 1, v_currRecDepth_3039_);
lean_ctor_set(v___x_3045_, 2, v_ref_3044_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*3, v_diag_3041_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*3 + 1, v_suppressElabErrors_3042_);
v___x_3046_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3037_, v___x_3043_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v___x_3045_, v_a_3030_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v_a_3049_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; uint8_t v___y_3060_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___x_3144_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v___x_3048_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_a_3047_, v_a_3028_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref(v___x_3048_);
v___x_3144_ = l_Lean_Expr_hasSorry(v_a_3049_);
if (v___x_3144_ == 0)
{
v___y_3089_ = v_a_3025_;
v___y_3090_ = v_a_3026_;
v___y_3091_ = v_a_3027_;
v___y_3092_ = v_a_3028_;
v___y_3093_ = v___x_3045_;
v___y_3094_ = v_a_3030_;
goto v___jp_3088_;
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = l_Lean_Expr_hasSyntheticSorry(v_a_3049_);
if (v___x_3145_ == 0)
{
v___y_3126_ = v_a_3025_;
v___y_3127_ = v_a_3026_;
v___y_3128_ = v_a_3027_;
v___y_3129_ = v_a_3028_;
v___y_3130_ = v___x_3045_;
v___y_3131_ = v_a_3030_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3146_; lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_3049_);
lean_dec_ref_known(v___x_3045_, 3);
v___x_3146_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
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
v___jp_3050_:
{
if (v___y_3060_ == 0)
{
if (lean_obj_tag(v___y_3055_) == 0)
{
lean_dec_ref_known(v___y_3055_, 2);
lean_dec_ref(v___y_3056_);
lean_dec(v_a_3049_);
return v___y_3059_;
}
else
{
lean_object* v_id_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3074_; 
v_id_3061_ = lean_ctor_get(v___y_3055_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___y_3055_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___y_3055_, 1);
lean_dec(v_unused_3075_);
v___x_3063_ = v___y_3055_;
v_isShared_3064_ = v_isSharedCheck_3074_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_id_3061_);
lean_dec(v___y_3055_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3074_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
uint8_t v___x_3065_; 
v___x_3065_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3058_, v_id_3061_);
lean_dec(v_id_3061_);
if (v___x_3065_ == 0)
{
lean_del_object(v___x_3063_);
lean_dec_ref(v___y_3056_);
lean_dec(v_a_3049_);
return v___y_3059_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
lean_dec_ref(v___y_3059_);
v___x_3066_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4);
v___x_3067_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6);
v___x_3068_ = l_Lean_indentExpr(v_a_3049_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 7);
lean_ctor_set(v___x_3063_, 1, v___x_3068_);
lean_ctor_set(v___x_3063_, 0, v___x_3067_);
v___x_3070_ = v___x_3063_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3066_);
v___x_3072_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3071_, v___y_3053_, v___y_3051_, v___y_3052_, v___y_3057_, v___y_3056_, v___y_3054_);
lean_dec_ref(v___y_3056_);
return v___x_3072_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v_a_3049_);
return v___y_3059_;
}
}
v___jp_3076_:
{
lean_object* v___x_3083_; 
lean_inc(v_a_3049_);
v___x_3083_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_3049_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_dec_ref(v___y_3081_);
lean_dec(v_a_3049_);
return v___x_3083_;
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
v___x_3085_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3086_ = l_Lean_Exception_isInterrupt(v_a_3084_);
if (v___x_3086_ == 0)
{
uint8_t v___x_3087_; 
lean_inc(v_a_3084_);
v___x_3087_ = l_Lean_Exception_isRuntime(v_a_3084_);
v___y_3051_ = v___y_3078_;
v___y_3052_ = v___y_3079_;
v___y_3053_ = v___y_3077_;
v___y_3054_ = v___y_3082_;
v___y_3055_ = v_a_3084_;
v___y_3056_ = v___y_3081_;
v___y_3057_ = v___y_3080_;
v___y_3058_ = v___x_3085_;
v___y_3059_ = v___x_3083_;
v___y_3060_ = v___x_3087_;
goto v___jp_3050_;
}
else
{
v___y_3051_ = v___y_3078_;
v___y_3052_ = v___y_3079_;
v___y_3053_ = v___y_3077_;
v___y_3054_ = v___y_3082_;
v___y_3055_ = v_a_3084_;
v___y_3056_ = v___y_3081_;
v___y_3057_ = v___y_3080_;
v___y_3058_ = v___x_3085_;
v___y_3059_ = v___x_3083_;
v___y_3060_ = v___x_3086_;
goto v___jp_3050_;
}
}
}
v___jp_3088_:
{
lean_object* v___x_3095_; 
lean_inc(v_a_3049_);
v___x_3095_ = l_Lean_Meta_getMVars(v_a_3049_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_3096_, v___x_3034_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v_a_3096_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; uint8_t v___x_3099_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v___x_3099_ = lean_unbox(v_a_3098_);
lean_dec(v_a_3098_);
if (v___x_3099_ == 0)
{
v___y_3077_ = v___y_3089_;
v___y_3078_ = v___y_3090_;
v___y_3079_ = v___y_3091_;
v___y_3080_ = v___y_3092_;
v___y_3081_ = v___y_3093_;
v___y_3082_ = v___y_3094_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3100_; lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3049_);
v___x_3100_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3049_);
v_a_3109_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3097_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3097_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v___y_3093_);
lean_dec(v_a_3049_);
v_a_3117_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3095_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3095_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
v___jp_3125_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v___x_3132_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8);
v___x_3133_ = l_Lean_indentExpr(v_a_3049_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3134_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec_ref(v___y_3130_);
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref_known(v___x_3045_, 3);
v_a_3155_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3046_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3046_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_stx_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(lean_object* v_config_3203_, lean_object* v_item_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_item_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3223_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_3204_, v___x_3222_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3223_) == 0)
{
uint8_t v___x_3224_; 
lean_dec_ref_known(v___x_3223_, 1);
v___x_3224_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3204_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3225_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3204_);
lean_inc_ref(v_item_3204_);
v___x_3226_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3204_);
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_3228_ = lean_string_dec_eq(v___x_3225_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_3230_ = lean_string_dec_eq(v___x_3225_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_3232_ = lean_string_dec_eq(v___x_3225_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_3234_ = lean_string_dec_eq(v___x_3225_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_3236_ = lean_string_dec_eq(v___x_3225_, v___x_3235_);
lean_dec_ref(v___x_3225_);
if (v___x_3236_ == 0)
{
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_item_3213_ = v___x_3226_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_3238_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3204_, v___x_3237_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3238_) == 0)
{
uint8_t v___x_3239_; 
lean_dec_ref_known(v___x_3238_, 1);
v___x_3239_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3226_);
if (v___x_3239_ == 0)
{
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_item_3213_ = v___x_3226_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3240_; 
lean_dec_ref(v___x_3226_);
v___x_3240_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3259_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3259_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3259_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
uint8_t v_kernel_3245_; uint8_t v_native_3246_; uint8_t v_revert_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3258_; 
v_kernel_3245_ = lean_ctor_get_uint8(v_config_3203_, 0);
v_native_3246_ = lean_ctor_get_uint8(v_config_3203_, 1);
v_revert_3247_ = lean_ctor_get_uint8(v_config_3203_, 3);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_config_3203_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3249_ = v_config_3203_;
v_isShared_3250_ = v_isSharedCheck_3258_;
goto v_resetjp_3248_;
}
else
{
lean_dec(v_config_3203_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3258_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3257_, 0, v_kernel_3245_);
lean_ctor_set_uint8(v_reuseFailAlloc_3257_, 1, v_native_3246_);
v___x_3252_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
uint8_t v___x_3253_; lean_object* v___x_3255_; 
v___x_3253_ = lean_unbox(v_a_3241_);
lean_dec(v_a_3241_);
lean_ctor_set_uint8(v___x_3252_, 2, v___x_3253_);
lean_ctor_set_uint8(v___x_3252_, 3, v_revert_3247_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3252_);
v___x_3255_ = v___x_3243_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3252_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v_config_3203_);
v_a_3260_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3240_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3240_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v___x_3226_);
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_a_3268_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3238_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3238_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec_ref(v___x_3225_);
v___x_3276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_3277_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3204_, v___x_3276_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3277_) == 0)
{
uint8_t v___x_3278_; 
lean_dec_ref_known(v___x_3277_, 1);
v___x_3278_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3226_);
if (v___x_3278_ == 0)
{
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_item_3213_ = v___x_3226_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3279_; 
lean_dec_ref(v___x_3226_);
v___x_3279_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3298_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3298_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3298_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
uint8_t v_kernel_3284_; uint8_t v_native_3285_; uint8_t v_zetaReduce_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3297_; 
v_kernel_3284_ = lean_ctor_get_uint8(v_config_3203_, 0);
v_native_3285_ = lean_ctor_get_uint8(v_config_3203_, 1);
v_zetaReduce_3286_ = lean_ctor_get_uint8(v_config_3203_, 2);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_config_3203_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3288_ = v_config_3203_;
v_isShared_3289_ = v_isSharedCheck_3297_;
goto v_resetjp_3287_;
}
else
{
lean_dec(v_config_3203_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3297_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3296_, 0, v_kernel_3284_);
lean_ctor_set_uint8(v_reuseFailAlloc_3296_, 1, v_native_3285_);
lean_ctor_set_uint8(v_reuseFailAlloc_3296_, 2, v_zetaReduce_3286_);
v___x_3291_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
uint8_t v___x_3292_; lean_object* v___x_3294_; 
v___x_3292_ = lean_unbox(v_a_3280_);
lean_dec(v_a_3280_);
lean_ctor_set_uint8(v___x_3291_, 3, v___x_3292_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3291_);
v___x_3294_ = v___x_3282_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3291_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v_config_3203_);
v_a_3299_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3279_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3279_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec_ref(v___x_3226_);
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_a_3307_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3277_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3277_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___x_3225_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_3316_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3204_, v___x_3315_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3316_) == 0)
{
uint8_t v___x_3317_; 
lean_dec_ref_known(v___x_3316_, 1);
v___x_3317_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3226_);
if (v___x_3317_ == 0)
{
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_item_3213_ = v___x_3226_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3318_; 
lean_dec_ref(v___x_3226_);
v___x_3318_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3337_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3337_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3337_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
uint8_t v_kernel_3323_; uint8_t v_zetaReduce_3324_; uint8_t v_revert_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3336_; 
v_kernel_3323_ = lean_ctor_get_uint8(v_config_3203_, 0);
v_zetaReduce_3324_ = lean_ctor_get_uint8(v_config_3203_, 2);
v_revert_3325_ = lean_ctor_get_uint8(v_config_3203_, 3);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_config_3203_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3327_ = v_config_3203_;
v_isShared_3328_ = v_isSharedCheck_3336_;
goto v_resetjp_3326_;
}
else
{
lean_dec(v_config_3203_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3336_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3335_, 0, v_kernel_3323_);
v___x_3330_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
uint8_t v___x_3331_; lean_object* v___x_3333_; 
v___x_3331_ = lean_unbox(v_a_3319_);
lean_dec(v_a_3319_);
lean_ctor_set_uint8(v___x_3330_, 1, v___x_3331_);
lean_ctor_set_uint8(v___x_3330_, 2, v_zetaReduce_3324_);
lean_ctor_set_uint8(v___x_3330_, 3, v_revert_3325_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3330_);
v___x_3333_ = v___x_3321_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3330_);
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
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v_config_3203_);
v_a_3338_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3318_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3318_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v___x_3226_);
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_a_3346_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3316_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3316_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec_ref(v___x_3225_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_3355_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_3204_, v___x_3354_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3355_) == 0)
{
uint8_t v___x_3356_; 
lean_dec_ref_known(v___x_3355_, 1);
v___x_3356_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3226_);
if (v___x_3356_ == 0)
{
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_item_3213_ = v___x_3226_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3357_; 
lean_dec_ref(v___x_3226_);
v___x_3357_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3376_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3376_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3376_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint8_t v_native_3362_; uint8_t v_zetaReduce_3363_; uint8_t v_revert_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3375_; 
v_native_3362_ = lean_ctor_get_uint8(v_config_3203_, 1);
v_zetaReduce_3363_ = lean_ctor_get_uint8(v_config_3203_, 2);
v_revert_3364_ = lean_ctor_get_uint8(v_config_3203_, 3);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_config_3203_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3366_ = v_config_3203_;
v_isShared_3367_ = v_isSharedCheck_3375_;
goto v_resetjp_3365_;
}
else
{
lean_dec(v_config_3203_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3375_;
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
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 0, 4);
v___x_3369_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
uint8_t v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_unbox(v_a_3358_);
lean_dec(v_a_3358_);
lean_ctor_set_uint8(v___x_3369_, 0, v___x_3370_);
lean_ctor_set_uint8(v___x_3369_, 1, v_native_3362_);
lean_ctor_set_uint8(v___x_3369_, 2, v_zetaReduce_3363_);
lean_ctor_set_uint8(v___x_3369_, 3, v_revert_3364_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3369_);
v___x_3372_ = v___x_3360_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3369_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_config_3203_);
v_a_3377_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3357_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3357_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___x_3226_);
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_a_3385_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3355_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3355_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
else
{
uint8_t v___x_3393_; 
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_config_3203_);
v___x_3393_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3226_);
if (v___x_3393_ == 0)
{
lean_dec_ref(v_item_3204_);
v_item_3213_ = v___x_3226_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
else
{
lean_object* v_value_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v___x_3226_);
v_value_3394_ = lean_ctor_get(v_item_3204_, 2);
lean_inc(v_value_3394_);
lean_dec_ref(v_item_3204_);
v___x_3395_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_value_3394_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3395_;
}
}
}
else
{
lean_dec_ref(v_config_3203_);
v_item_3213_ = v_item_3204_;
v___y_3214_ = v___y_3205_;
v___y_3215_ = v___y_3206_;
v___y_3216_ = v___y_3207_;
v___y_3217_ = v___y_3208_;
v___y_3218_ = v___y_3209_;
v___y_3219_ = v___y_3210_;
goto v___jp_3212_;
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_item_3204_);
lean_dec_ref(v_config_3203_);
v_a_3396_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3223_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3223_);
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
v___jp_3212_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_3221_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_3213_, v___x_3220_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_3404_, lean_object* v_item_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(v_config_3404_, v_item_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_00_u03b1_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(v_00_u03b1_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3433_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = lean_box(0);
v___x_3435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5));
v___x_3436_ = l_Lean_mkConst(v___x_3435_, v___x_3434_);
return v___x_3436_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(lean_object* v_cfg_3439_, lean_object* v_cfgItem_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1);
v___x_3449_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_3439_, v_cfgItem_3440_, v___x_3448_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_3450_, lean_object* v_cfgItem_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(v_cfg_3450_, v_cfgItem_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v_cfgItem_3451_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object* v_cfg_3461_, lean_object* v_init_3462_, uint8_t v_logExceptions_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_onErr_3468_; lean_object* v_eval_3469_; 
v_onErr_3468_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0));
v_eval_3469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_3463_ == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3469_, v_init_3462_, v_cfg_3461_, v_onErr_3468_, v_logExceptions_3463_, v_a_3465_, v_a_3466_);
return v___x_3470_;
}
else
{
uint8_t v_recover_3471_; lean_object* v___x_3472_; 
v_recover_3471_ = lean_ctor_get_uint8(v_a_3464_, sizeof(void*)*1);
v___x_3472_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_3469_, v_init_3462_, v_cfg_3461_, v_onErr_3468_, v_recover_3471_, v_a_3465_, v_a_3466_);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object* v_cfg_3473_, lean_object* v_init_3474_, lean_object* v_logExceptions_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
uint8_t v_logExceptions_boxed_3480_; lean_object* v_res_3481_; 
v_logExceptions_boxed_3480_ = lean_unbox(v_logExceptions_3475_);
v_res_3481_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_cfg_3473_, v_init_3474_, v_logExceptions_boxed_3480_, v_a_3476_, v_a_3477_, v_a_3478_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec_ref(v_a_3476_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* v_cfg_3482_, lean_object* v_init_3483_, uint8_t v_logExceptions_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_cfg_3482_, v_init_3483_, v_logExceptions_3484_, v_a_3485_, v_a_3491_, v_a_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* v_cfg_3495_, lean_object* v_init_3496_, lean_object* v_logExceptions_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
uint8_t v_logExceptions_boxed_3507_; lean_object* v_res_3508_; 
v_logExceptions_boxed_3507_ = lean_unbox(v_logExceptions_3497_);
v_res_3508_ = l_Lean_Elab_Tactic_elabDecideConfig(v_cfg_3495_, v_init_3496_, v_logExceptions_boxed_3507_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* v_stx_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = l_Lean_Syntax_getArg(v_stx_3514_, v___x_3524_);
v___x_3526_ = 1;
v___x_3527_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__0));
v___x_3528_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3525_, v___x_3527_, v___x_3526_, v_a_3515_, v_a_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__1));
v___x_3531_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3530_, v_a_3529_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3529_);
return v___x_3531_;
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3528_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3528_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object* v_stx_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Elab_Tactic_evalDecide(v_stx_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_stx_3540_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3564_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0));
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
v___x_3568_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3564_, v___x_3565_, v___x_3566_, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6));
v___x_3599_ = l_Lean_addBuiltinDeclarationRanges(v___x_3597_, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* v_stx_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = l_Lean_Syntax_getArg(v_stx_3605_, v___x_3615_);
v___x_3617_ = 1;
v___x_3618_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__0));
v___x_3619_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3616_, v___x_3618_, v___x_3617_, v_a_3606_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; uint8_t v_kernel_3621_; uint8_t v_zetaReduce_3622_; uint8_t v_revert_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3632_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3619_, 1);
v_kernel_3621_ = lean_ctor_get_uint8(v_a_3620_, 0);
v_zetaReduce_3622_ = lean_ctor_get_uint8(v_a_3620_, 2);
v_revert_3623_ = lean_ctor_get_uint8(v_a_3620_, 3);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_a_3620_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3625_ = v_a_3620_;
v_isShared_3626_ = v_isSharedCheck_3632_;
goto v_resetjp_3624_;
}
else
{
lean_dec(v_a_3620_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3632_;
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
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3631_, 0, v_kernel_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3631_, 2, v_zetaReduce_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3631_, 3, v_revert_3623_);
v___x_3628_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_ctor_set_uint8(v___x_3628_, 1, v___x_3617_);
v___x_3629_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___closed__1));
v___x_3630_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3629_, v___x_3628_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec_ref(v___x_3628_);
return v___x_3630_;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
v_a_3633_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3619_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3619_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object* v_stx_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Elab_Tactic_evalNativeDecide(v_stx_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_stx_3641_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3665_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1));
v___x_3667_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
v___x_3669_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3665_, v___x_3666_, v___x_3667_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6));
v___x_3700_ = l_Lean_addBuiltinDeclarationRanges(v___x_3698_, v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
return v_res_3702_;
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
