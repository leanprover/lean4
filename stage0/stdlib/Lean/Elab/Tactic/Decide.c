// Lean compiler output
// Module: Lean.Elab.Tactic.Decide
// Imports: public import Lean.Elab.Tactic.Basic import Lean.Meta.Native import Lean.Elab.Tactic.ElabTerm
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "` failed for proposition"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nbecause its `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instance"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "\ndid not reduce to `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` or `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "`.\n\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value),LEAN_SCALAR_PTR_LITERAL(76, 246, 154, 249, 193, 98, 251, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Reduction got stuck on `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, which indicates that a `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "` instance is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. The `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "` tactic works by evaluating a decision procedure via reduction, and it cannot make progress with such instances. This can occur due to the `open scoped Classical` command, which enables the instance `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "propDecidable"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value),LEAN_SCALAR_PTR_LITERAL(166, 239, 88, 215, 135, 192, 113, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 28, .m_data = "Reduction got stuck on `▸` ("};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "), which suggests that one of the `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "` instances is defined using tactics such as `rw` or `simp`. To avoid tactics, make use of functions such as `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value),LEAN_SCALAR_PTR_LITERAL(120, 135, 37, 233, 184, 173, 222, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "decidable_of_decidable_of_iff"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value),LEAN_SCALAR_PTR_LITERAL(191, 29, 120, 93, 238, 147, 138, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` to alter a proposition."};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "After unfolding the "};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = ", reduction got stuck at the `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Reduction got stuck at the `"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` proved that the proposition"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "DecideConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(9, 154, 224, 188, 146, 89, 215, 198)}};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__6_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalDecide"};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(204, 31, 201, 122, 54, 242, 99, 241)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(373) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(397) << 1) | 1)),((lean_object*)(((size_t)(74) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value),((lean_object*)(((size_t)(74) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(373) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(373) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "native_decide"};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 101, 7, 237, 41, 103, 237, 127)}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeDecide"};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 229, 81, 15, 25, 144, 49, 103)}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalNativeDecide"};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 133, 224, 42, 29, 33, 56, 192)}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(410) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(417) << 1) | 1)),((lean_object*)(((size_t)(160) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value),((lean_object*)(((size_t)(160) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(410) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(410) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object*);
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
lean_dec_ref(v___x_86_);
if (lean_obj_tag(v_val_88_) == 1)
{
uint8_t v_v_89_; 
v_v_89_ = lean_ctor_get_uint8(v_val_88_, 0);
lean_dec_ref(v_val_88_);
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
lean_inc(v_macroStack_165_);
lean_dec_ref(v___y_155_);
lean_inc(v_macroStack_165_);
v___x_166_ = l_Lean_Elab_getBetterRef(v_ref_162_, v_macroStack_165_);
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
lean_inc(v_a_203_);
lean_inc_ref(v_a_202_);
lean_inc(v_a_201_);
lean_inc_ref(v_a_200_);
v___x_253_ = l_Lean_Meta_zetaReduce(v_a_251_, v___x_252_, v___x_252_, v___x_252_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref(v___x_253_);
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
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec_ref(v_a_198_);
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
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec_ref(v___y_207_);
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
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
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
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
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
lean_dec(v_a_257_);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
if (lean_obj_tag(v_x_330_) == 0)
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
else
{
if (lean_obj_tag(v_x_330_) == 0)
{
uint8_t v___x_333_; 
v___x_333_ = 0;
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v_val_335_; uint8_t v___x_336_; 
v_val_334_ = lean_ctor_get(v_x_329_, 0);
v_val_335_ = lean_ctor_get(v_x_330_, 0);
v___x_336_ = lean_name_eq(v_val_334_, v_val_335_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_x_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec(v_x_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = l_Lean_maxRecDepthErrorMessage;
v___x_347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3);
v___x_349_ = l_Lean_MessageData_ofFormat(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4);
v___x_351_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2));
v___x_352_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(lean_object* v_ref_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v_ref_353_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___boxed(lean_object* v_ref_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3(lean_object* v_00_u03b1_361_, lean_object* v_ref_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_362_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___boxed(lean_object* v_00_u03b1_369_, lean_object* v_ref_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3(v_00_u03b1_369_, v_ref_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4(void){
_start:
{
lean_object* v___x_385_; lean_object* v_dummy_386_; 
v___x_385_ = lean_box(0);
v_dummy_386_ = l_Lean_Expr_sort___override(v___x_385_);
return v_dummy_386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object* v_upperBound_399_, lean_object* v_val_400_, lean_object* v___x_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_a_406_, lean_object* v_b_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_a_414_; uint8_t v___x_418_; 
v___x_418_ = lean_nat_dec_lt(v_a_406_, v_upperBound_399_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v_a_406_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_b_407_);
return v___x_419_;
}
else
{
lean_object* v_numParams_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v_b_407_);
v_numParams_420_ = lean_ctor_get(v_val_400_, 0);
v___x_421_ = l_Lean_instInhabitedExpr;
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_numParams_420_, v___x_422_);
v___x_424_ = lean_nat_add(v___x_423_, v_a_406_);
lean_dec(v___x_423_);
v___x_425_ = lean_array_get_borrowed(v___x_421_, v___x_401_, v___x_424_);
lean_dec(v___x_424_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___x_425_);
v___x_426_ = lean_infer_type(v___x_425_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v___x_426_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
v___x_428_ = l_Lean_Meta_isClass_x3f(v_a_427_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
v___x_430_ = lean_box(0);
v___x_431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3));
v___x_432_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1));
v___x_433_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_a_429_, v___x_432_);
lean_dec(v_a_429_);
if (v___x_433_ == 0)
{
v_a_414_ = v___x_431_;
goto v___jp_413_;
}
else
{
lean_object* v___x_434_; 
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___x_425_);
v___x_434_ = lean_whnf(v___x_425_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; uint8_t v___y_437_; uint8_t v___x_457_; uint8_t v___y_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v___x_434_);
v___x_457_ = lean_nat_dec_eq(v___x_402_, v___x_403_);
v___x_460_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3));
v___x_461_ = l_Lean_Expr_isAppOf(v_a_435_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5));
v___x_463_ = l_Lean_Expr_isAppOf(v_a_435_, v___x_462_);
v___y_459_ = v___x_463_;
goto v___jp_458_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_eq(v___x_404_, v___x_405_);
v___y_459_ = v___x_464_;
goto v___jp_458_;
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
lean_dec(v_a_435_);
v_a_414_ = v___x_431_;
goto v___jp_413_;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_a_406_);
v___x_438_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_435_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_448_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_448_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_a_439_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_430_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_444_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_438_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_438_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
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
v___jp_458_:
{
if (v___y_459_ == 0)
{
v___y_437_ = v___x_433_;
goto v___jp_436_;
}
else
{
v___y_437_ = v___x_457_;
goto v___jp_436_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v_a_406_);
v_a_465_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_434_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_434_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
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
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v_a_406_);
v_a_473_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_428_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_428_);
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
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v_a_406_);
v_a_481_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_426_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_426_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
v___jp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_a_406_, v___x_415_);
lean_dec(v_a_406_);
v_a_406_ = v___x_416_;
v_b_407_ = v_a_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* v_inst_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_fileName_495_; lean_object* v_fileMap_496_; lean_object* v_options_497_; lean_object* v_currRecDepth_498_; lean_object* v_maxRecDepth_499_; lean_object* v_ref_500_; lean_object* v_currNamespace_501_; lean_object* v_openDecls_502_; lean_object* v_initHeartbeats_503_; lean_object* v_maxHeartbeats_504_; lean_object* v_quotContext_505_; lean_object* v_currMacroScope_506_; uint8_t v_diag_507_; lean_object* v_cancelTk_x3f_508_; uint8_t v_suppressElabErrors_509_; lean_object* v_inheritedTraceOptions_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_583_; 
v_fileName_495_ = lean_ctor_get(v_a_492_, 0);
v_fileMap_496_ = lean_ctor_get(v_a_492_, 1);
v_options_497_ = lean_ctor_get(v_a_492_, 2);
v_currRecDepth_498_ = lean_ctor_get(v_a_492_, 3);
v_maxRecDepth_499_ = lean_ctor_get(v_a_492_, 4);
v_ref_500_ = lean_ctor_get(v_a_492_, 5);
v_currNamespace_501_ = lean_ctor_get(v_a_492_, 6);
v_openDecls_502_ = lean_ctor_get(v_a_492_, 7);
v_initHeartbeats_503_ = lean_ctor_get(v_a_492_, 8);
v_maxHeartbeats_504_ = lean_ctor_get(v_a_492_, 9);
v_quotContext_505_ = lean_ctor_get(v_a_492_, 10);
v_currMacroScope_506_ = lean_ctor_get(v_a_492_, 11);
v_diag_507_ = lean_ctor_get_uint8(v_a_492_, sizeof(void*)*14);
v_cancelTk_x3f_508_ = lean_ctor_get(v_a_492_, 12);
v_suppressElabErrors_509_ = lean_ctor_get_uint8(v_a_492_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_510_ = lean_ctor_get(v_a_492_, 13);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_583_ == 0)
{
v___x_512_ = v_a_492_;
v_isShared_513_ = v_isSharedCheck_583_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_inheritedTraceOptions_510_);
lean_inc(v_cancelTk_x3f_508_);
lean_inc(v_currMacroScope_506_);
lean_inc(v_quotContext_505_);
lean_inc(v_maxHeartbeats_504_);
lean_inc(v_initHeartbeats_503_);
lean_inc(v_openDecls_502_);
lean_inc(v_currNamespace_501_);
lean_inc(v_ref_500_);
lean_inc(v_maxRecDepth_499_);
lean_inc(v_currRecDepth_498_);
lean_inc(v_options_497_);
lean_inc(v_fileMap_496_);
lean_inc(v_fileName_495_);
lean_dec(v_a_492_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_583_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = lean_nat_dec_eq(v_currRecDepth_498_, v_maxRecDepth_499_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_currRecDepth_498_, v___x_515_);
lean_inc(v_maxRecDepth_499_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v___x_516_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_fileName_495_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_fileMap_496_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_options_497_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_maxRecDepth_499_);
lean_ctor_set(v_reuseFailAlloc_581_, 5, v_ref_500_);
lean_ctor_set(v_reuseFailAlloc_581_, 6, v_currNamespace_501_);
lean_ctor_set(v_reuseFailAlloc_581_, 7, v_openDecls_502_);
lean_ctor_set(v_reuseFailAlloc_581_, 8, v_initHeartbeats_503_);
lean_ctor_set(v_reuseFailAlloc_581_, 9, v_maxHeartbeats_504_);
lean_ctor_set(v_reuseFailAlloc_581_, 10, v_quotContext_505_);
lean_ctor_set(v_reuseFailAlloc_581_, 11, v_currMacroScope_506_);
lean_ctor_set(v_reuseFailAlloc_581_, 12, v_cancelTk_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_581_, 13, v_inheritedTraceOptions_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*14, v_diag_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*14 + 1, v_suppressElabErrors_509_);
v___x_518_ = v_reuseFailAlloc_581_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
lean_inc(v_a_493_);
lean_inc_ref(v___x_518_);
lean_inc(v_a_491_);
lean_inc_ref(v_a_490_);
v___x_519_ = lean_whnf(v_inst_489_, v_a_490_, v_a_491_, v___x_518_, v_a_493_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
v___x_521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2));
v___x_522_ = lean_unsigned_to_nat(5u);
v___x_523_ = l_Lean_Expr_isAppOfArity(v_a_520_, v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Expr_getAppFn(v_a_520_);
if (lean_obj_tag(v___x_524_) == 4)
{
lean_object* v_declName_525_; lean_object* v___x_526_; 
lean_dec_ref(v___x_519_);
v_declName_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_declName_525_);
lean_dec_ref(v___x_524_);
v___x_526_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_525_, v_a_493_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_570_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_570_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_570_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_570_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
if (lean_obj_tag(v_a_527_) == 1)
{
lean_object* v_val_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_val_531_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_val_531_);
lean_dec_ref(v_a_527_);
v___x_532_ = l_Lean_Expr_getAppNumArgs(v_a_520_);
v___x_533_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_531_);
v___x_534_ = lean_nat_dec_eq(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_536_; 
lean_dec(v___x_533_);
lean_dec(v___x_532_);
lean_dec(v_val_531_);
lean_dec_ref(v___x_518_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_a_520_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_520_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v_numDiscrs_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_dummy_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_del_object(v___x_529_);
v_numDiscrs_538_ = lean_ctor_get(v_val_531_, 1);
lean_inc(v_numDiscrs_538_);
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3));
v_dummy_541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__4);
lean_inc(v___x_532_);
v___x_542_ = lean_mk_array(v___x_532_, v_dummy_541_);
v___x_543_ = lean_nat_sub(v___x_532_, v___x_515_);
lean_inc(v_a_520_);
v___x_544_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_520_, v___x_542_, v___x_543_);
v___x_545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_numDiscrs_538_, v_val_531_, v___x_544_, v_currRecDepth_498_, v_maxRecDepth_499_, v___x_532_, v___x_533_, v___x_539_, v___x_540_, v_a_490_, v_a_491_, v___x_518_, v_a_493_);
lean_dec(v___x_533_);
lean_dec(v___x_532_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec_ref(v___x_544_);
lean_dec(v_val_531_);
lean_dec(v_numDiscrs_538_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_558_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_558_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_558_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_558_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_fst_550_; 
v_fst_550_ = lean_ctor_get(v_a_546_, 0);
lean_inc(v_fst_550_);
lean_dec(v_a_546_);
if (lean_obj_tag(v_fst_550_) == 0)
{
lean_object* v___x_552_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v_a_520_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_520_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v_val_554_; lean_object* v___x_556_; 
lean_dec(v_a_520_);
v_val_554_ = lean_ctor_get(v_fst_550_, 0);
lean_inc(v_val_554_);
lean_dec_ref(v_fst_550_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v_val_554_);
v___x_556_ = v___x_548_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_val_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v_a_520_);
v_a_559_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_545_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_545_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v_a_527_);
lean_dec_ref(v___x_518_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_a_520_);
v___x_568_ = v___x_529_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_520_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_a_520_);
lean_dec_ref(v___x_518_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
v_a_571_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_526_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_526_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_dec_ref(v___x_524_);
lean_dec(v_a_520_);
lean_dec_ref(v___x_518_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
return v___x_519_;
}
}
else
{
lean_object* v___x_579_; 
lean_dec_ref(v___x_519_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
v___x_579_ = l_Lean_Expr_appArg_x21(v_a_520_);
lean_dec(v_a_520_);
v_inst_489_ = v___x_579_;
v_a_492_ = v___x_518_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_518_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
return v___x_519_;
}
}
}
else
{
lean_object* v___x_582_; 
lean_del_object(v___x_512_);
lean_dec_ref(v_inheritedTraceOptions_510_);
lean_dec(v_cancelTk_x3f_508_);
lean_dec(v_currMacroScope_506_);
lean_dec(v_quotContext_505_);
lean_dec(v_maxHeartbeats_504_);
lean_dec(v_initHeartbeats_503_);
lean_dec(v_openDecls_502_);
lean_dec(v_currNamespace_501_);
lean_dec(v_maxRecDepth_499_);
lean_dec(v_currRecDepth_498_);
lean_dec_ref(v_options_497_);
lean_dec_ref(v_fileMap_496_);
lean_dec_ref(v_fileName_495_);
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec_ref(v_inst_489_);
v___x_582_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_500_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object* v_inst_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_inst_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object* v_upperBound_591_, lean_object* v_val_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_a_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_upperBound_591_, v_val_592_, v___x_593_, v___x_594_, v___x_595_, v___x_596_, v___x_597_, v_a_598_, v_b_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___x_597_);
lean_dec(v___x_596_);
lean_dec(v___x_595_);
lean_dec(v___x_594_);
lean_dec_ref(v___x_593_);
lean_dec_ref(v_val_592_);
lean_dec(v_upperBound_591_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object* v_upperBound_606_, lean_object* v_val_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_inst_613_, lean_object* v_R_614_, lean_object* v_a_615_, lean_object* v_b_616_, lean_object* v_c_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_upperBound_606_, v_val_607_, v___x_608_, v___x_609_, v___x_610_, v___x_611_, v___x_612_, v_a_615_, v_b_616_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_624_ = _args[0];
lean_object* v_val_625_ = _args[1];
lean_object* v___x_626_ = _args[2];
lean_object* v___x_627_ = _args[3];
lean_object* v___x_628_ = _args[4];
lean_object* v___x_629_ = _args[5];
lean_object* v___x_630_ = _args[6];
lean_object* v_inst_631_ = _args[7];
lean_object* v_R_632_ = _args[8];
lean_object* v_a_633_ = _args[9];
lean_object* v_b_634_ = _args[10];
lean_object* v_c_635_ = _args[11];
lean_object* v___y_636_ = _args[12];
lean_object* v___y_637_ = _args[13];
lean_object* v___y_638_ = _args[14];
lean_object* v___y_639_ = _args[15];
lean_object* v___y_640_ = _args[16];
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(v_upperBound_624_, v_val_625_, v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_630_, v_inst_631_, v_R_632_, v_a_633_, v_b_634_, v_c_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___x_630_);
lean_dec(v___x_629_);
lean_dec(v___x_628_);
lean_dec(v___x_627_);
lean_dec_ref(v___x_626_);
lean_dec_ref(v_val_625_);
lean_dec(v_upperBound_624_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_ref_648_; lean_object* v___x_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_ref_648_ = lean_ctor_get(v___y_645_, 5);
v___x_649_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_inc(v_ref_648_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v_ref_648_);
lean_ctor_set(v___x_654_, 1, v_a_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 1);
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_box(0);
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1));
v___x_671_ = l_Lean_mkConst(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore(lean_object* v_tacticName_681_, lean_object* v_expectedType_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_692_; 
lean_inc(v_a_690_);
lean_inc_ref(v_a_689_);
lean_inc(v_a_688_);
lean_inc_ref(v_a_687_);
lean_inc_ref(v_expectedType_682_);
v___x_692_ = l_Lean_Meta_mkDecide(v_expectedType_682_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_732_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_732_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_732_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_732_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_ref_697_; lean_object* v___x_699_; 
v_ref_697_ = lean_ctor_get(v_a_689_, 5);
lean_inc(v_ref_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set_tag(v___x_695_, 1);
lean_ctor_set(v___x_695_, 0, v_ref_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_ref_697_);
v___x_699_ = v_reuseFailAlloc_731_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
lean_inc(v_a_690_);
lean_inc_ref(v_a_689_);
lean_inc(v_a_688_);
lean_inc_ref(v_a_687_);
lean_inc(v_a_693_);
lean_inc(v_tacticName_681_);
v___x_700_ = l_Lean_Meta_nativeEqTrue(v_tacticName_681_, v_a_693_, v___x_699_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v___x_699_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_722_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_722_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_722_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_722_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
if (lean_obj_tag(v_a_701_) == 0)
{
lean_object* v_prf_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_tacticName_681_);
v_prf_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_prf_705_);
lean_dec_ref(v_a_701_);
v___x_706_ = l_Lean_Expr_appArg_x21(v_a_693_);
lean_dec(v_a_693_);
v___x_707_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_708_ = l_Lean_mkApp3(v___x_707_, v_expectedType_682_, v___x_706_, v_prf_705_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_708_);
v___x_710_ = v___x_703_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_del_object(v___x_703_);
lean_dec(v_a_693_);
v___x_712_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_713_ = l_Lean_MessageData_ofName(v_tacticName_681_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_indentExpr(v_expectedType_682_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_720_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
return v___x_721_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_693_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec_ref(v_expectedType_682_);
lean_dec(v_tacticName_681_);
v_a_723_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_700_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_700_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec_ref(v_expectedType_682_);
lean_dec(v_tacticName_681_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(lean_object* v_tacticName_733_, lean_object* v_expectedType_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_733_, v_expectedType_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(lean_object* v_00_u03b1_745_, lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_746_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(lean_object* v_00_u03b1_757_, lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(v_00_u03b1_757_, v_msg_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object* v_opts_769_, lean_object* v_opt_770_){
_start:
{
lean_object* v_name_771_; lean_object* v_defValue_772_; lean_object* v_map_773_; lean_object* v___x_774_; 
v_name_771_ = lean_ctor_get(v_opt_770_, 0);
v_defValue_772_ = lean_ctor_get(v_opt_770_, 1);
v_map_773_ = lean_ctor_get(v_opts_769_, 0);
v___x_774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_773_, v_name_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_inc(v_defValue_772_);
return v_defValue_772_;
}
else
{
lean_object* v_val_775_; 
v_val_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_val_775_);
lean_dec_ref(v___x_774_);
if (lean_obj_tag(v_val_775_) == 3)
{
lean_object* v_v_776_; 
v_v_776_ = lean_ctor_get(v_val_775_, 0);
lean_inc(v_v_776_);
lean_dec_ref(v_val_775_);
return v_v_776_;
}
else
{
lean_dec(v_val_775_);
lean_inc(v_defValue_772_);
return v_defValue_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object* v_opts_777_, lean_object* v_opt_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_opts_777_, v_opt_778_);
lean_dec_ref(v_opt_778_);
lean_dec_ref(v_opts_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_saveState___redArg(v___y_782_, v___y_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v_r_788_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_786_);
lean_inc(v___y_784_);
lean_inc(v___y_782_);
v_r_788_ = lean_apply_5(v_x_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
if (lean_obj_tag(v_r_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v_r_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v_r_788_);
v___x_790_ = l_Lean_Meta_SavedState_restore___redArg(v_a_787_, v___y_782_, v___y_784_);
lean_dec(v___y_784_);
lean_dec(v___y_782_);
lean_dec(v_a_787_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_790_, 0);
lean_dec(v_unused_798_);
v___x_792_ = v___x_790_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_dec(v___x_790_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_a_789_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_789_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_789_);
v_a_799_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_790_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_790_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_ctor_get(v_r_788_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v_r_788_);
v___x_808_ = l_Lean_Meta_SavedState_restore___redArg(v_a_787_, v___y_782_, v___y_784_);
lean_dec(v___y_784_);
lean_dec(v___y_782_);
lean_dec(v_a_787_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_808_, 0);
lean_dec(v_unused_816_);
v___x_810_ = v___x_808_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_dec(v___x_808_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 1);
lean_ctor_set(v___x_810_, 0, v_a_807_);
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_807_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_a_807_);
v_a_817_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_808_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_808_);
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
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_x_780_);
v_a_825_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_786_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_786_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_x_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object* v_00_u03b1_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object* v_00_u03b1_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_00_u03b1_848_, v_x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object* v_cs_856_, lean_object* v_n_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_array_push(v_cs_856_, v_n_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object* v_cs_860_, lean_object* v_n_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(v_cs_860_, v_n_861_, v_x_862_);
lean_dec(v_x_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object* v_o_867_, lean_object* v_k_868_, uint8_t v_v_869_){
_start:
{
lean_object* v_map_870_; uint8_t v_hasTrace_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_885_; 
v_map_870_ = lean_ctor_get(v_o_867_, 0);
v_hasTrace_871_ = lean_ctor_get_uint8(v_o_867_, sizeof(void*)*1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_o_867_);
if (v_isSharedCheck_885_ == 0)
{
v___x_873_ = v_o_867_;
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_map_870_);
lean_dec(v_o_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_875_, 0, v_v_869_);
lean_inc(v_k_868_);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_868_, v___x_875_, v_map_870_);
if (v_hasTrace_871_ == 0)
{
lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_880_; 
v___x_877_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1));
v___x_878_ = l_Lean_Name_isPrefixOf(v___x_877_, v_k_868_);
lean_dec(v_k_868_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_880_ = v___x_873_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_876_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1, v___x_878_);
return v___x_880_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec(v_k_868_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_883_ = v___x_873_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_884_, sizeof(void*)*1, v_hasTrace_871_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object* v_o_886_, lean_object* v_k_887_, lean_object* v_v_888_){
_start:
{
uint8_t v_v_boxed_889_; lean_object* v_res_890_; 
v_v_boxed_889_ = lean_unbox(v_v_888_);
v_res_890_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_o_886_, v_k_887_, v_v_boxed_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object* v_opts_891_, lean_object* v_opt_892_, uint8_t v_val_893_){
_start:
{
lean_object* v_name_894_; lean_object* v___x_895_; 
v_name_894_ = lean_ctor_get(v_opt_892_, 0);
lean_inc(v_name_894_);
lean_dec_ref(v_opt_892_);
v___x_895_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_opts_891_, v_name_894_, v_val_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object* v_opts_896_, lean_object* v_opt_897_, lean_object* v_val_898_){
_start:
{
uint8_t v_val_boxed_899_; lean_object* v_res_900_; 
v_val_boxed_899_ = lean_unbox(v_val_898_);
v_res_900_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_opts_896_, v_opt_897_, v_val_boxed_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(lean_object* v_f_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_acc_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_keys_902_);
v___x_907_ = lean_nat_dec_lt(v_i_904_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec(v_i_904_);
lean_dec(v_f_901_);
return v_acc_905_;
}
else
{
lean_object* v_k_908_; lean_object* v_v_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_k_908_ = lean_array_fget_borrowed(v_keys_902_, v_i_904_);
v_v_909_ = lean_array_fget_borrowed(v_vals_903_, v_i_904_);
lean_inc(v_f_901_);
lean_inc(v_v_909_);
lean_inc(v_k_908_);
v___x_910_ = lean_apply_3(v_f_901_, v_acc_905_, v_k_908_, v_v_909_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_904_, v___x_911_);
lean_dec(v_i_904_);
v_i_904_ = v___x_912_;
v_acc_905_ = v___x_910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg___boxed(lean_object* v_f_914_, lean_object* v_keys_915_, lean_object* v_vals_916_, lean_object* v_i_917_, lean_object* v_acc_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_914_, v_keys_915_, v_vals_916_, v_i_917_, v_acc_918_);
lean_dec_ref(v_vals_916_);
lean_dec_ref(v_keys_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(lean_object* v_f_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v_es_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_es_923_ = lean_ctor_get(v_x_921_, 0);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_array_get_size(v_es_923_);
v___x_926_ = lean_nat_dec_lt(v___x_924_, v___x_925_);
if (v___x_926_ == 0)
{
lean_dec(v_f_920_);
return v_x_922_;
}
else
{
uint8_t v___x_927_; 
v___x_927_ = lean_nat_dec_le(v___x_925_, v___x_925_);
if (v___x_927_ == 0)
{
if (v___x_926_ == 0)
{
lean_dec(v_f_920_);
return v_x_922_;
}
else
{
size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((size_t)0ULL);
v___x_929_ = lean_usize_of_nat(v___x_925_);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_920_, v_es_923_, v___x_928_, v___x_929_, v_x_922_);
return v___x_930_;
}
}
else
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((size_t)0ULL);
v___x_932_ = lean_usize_of_nat(v___x_925_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_920_, v_es_923_, v___x_931_, v___x_932_, v_x_922_);
return v___x_933_;
}
}
}
else
{
lean_object* v_ks_934_; lean_object* v_vs_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_ks_934_ = lean_ctor_get(v_x_921_, 0);
v_vs_935_ = lean_ctor_get(v_x_921_, 1);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_920_, v_ks_934_, v_vs_935_, v___x_936_, v_x_922_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(lean_object* v_f_938_, lean_object* v_as_939_, size_t v_i_940_, size_t v_stop_941_, lean_object* v_b_942_){
_start:
{
lean_object* v___y_944_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_eq(v_i_940_, v_stop_941_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_array_uget_borrowed(v_as_939_, v_i_940_);
switch(lean_obj_tag(v___x_949_))
{
case 0:
{
lean_object* v_key_950_; lean_object* v_val_951_; lean_object* v___x_952_; 
v_key_950_ = lean_ctor_get(v___x_949_, 0);
v_val_951_ = lean_ctor_get(v___x_949_, 1);
lean_inc(v_f_938_);
lean_inc(v_val_951_);
lean_inc(v_key_950_);
v___x_952_ = lean_apply_3(v_f_938_, v_b_942_, v_key_950_, v_val_951_);
v___y_944_ = v___x_952_;
goto v___jp_943_;
}
case 1:
{
lean_object* v_node_953_; lean_object* v___x_954_; 
v_node_953_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_f_938_);
v___x_954_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_938_, v_node_953_, v_b_942_);
v___y_944_ = v___x_954_;
goto v___jp_943_;
}
default: 
{
v___y_944_ = v_b_942_;
goto v___jp_943_;
}
}
}
else
{
lean_dec(v_f_938_);
return v_b_942_;
}
v___jp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_940_, v___x_945_);
v_i_940_ = v___x_946_;
v_b_942_ = v___y_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_f_955_, lean_object* v_as_956_, lean_object* v_i_957_, lean_object* v_stop_958_, lean_object* v_b_959_){
_start:
{
size_t v_i_boxed_960_; size_t v_stop_boxed_961_; lean_object* v_res_962_; 
v_i_boxed_960_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_958_);
lean_dec(v_stop_958_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_955_, v_as_956_, v_i_boxed_960_, v_stop_boxed_961_, v_b_959_);
lean_dec_ref(v_as_956_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_f_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_963_, v_x_964_, v_x_965_);
lean_dec_ref(v_x_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0(lean_object* v_f_967_, lean_object* v_x1_968_, lean_object* v_x2_969_, lean_object* v_x3_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_apply_3(v_f_967_, v_x1_968_, v_x2_969_, v_x3_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(lean_object* v_map_972_, lean_object* v_f_973_, lean_object* v_init_974_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_975_, 0, v_f_973_);
v___x_976_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v___f_975_, v_map_972_, v_init_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___boxed(lean_object* v_map_977_, lean_object* v_f_978_, lean_object* v_init_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_977_, v_f_978_, v_init_979_);
lean_dec_ref(v_map_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(lean_object* v_as_982_, lean_object* v_lo_983_, lean_object* v_hi_984_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_lt(v_lo_983_, v_hi_984_);
if (v___x_985_ == 0)
{
lean_dec(v_lo_983_);
return v_as_982_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; uint8_t v___x_990_; 
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___closed__0));
lean_inc(v_lo_983_);
v___x_987_ = l_Array_qpartition___redArg(v_as_982_, v___x_986_, v_lo_983_, v_hi_984_);
v_fst_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_fst_988_);
v_snd_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_snd_989_);
lean_dec_ref(v___x_987_);
v___x_990_ = lean_nat_dec_le(v_hi_984_, v_fst_988_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_snd_989_, v_lo_983_, v_fst_988_);
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_add(v_fst_988_, v___x_992_);
lean_dec(v_fst_988_);
v_as_982_ = v___x_991_;
v_lo_983_ = v___x_993_;
goto _start;
}
else
{
lean_dec(v_fst_988_);
lean_dec(v_lo_983_);
return v_snd_989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(lean_object* v_as_995_, lean_object* v_lo_996_, lean_object* v_hi_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_as_995_, v_lo_996_, v_hi_997_);
lean_dec(v_hi_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
if (lean_obj_tag(v_a_999_) == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = l_List_reverse___redArg(v_a_1000_);
return v___x_1001_;
}
else
{
lean_object* v_head_1002_; lean_object* v_tail_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1012_; 
v_head_1002_ = lean_ctor_get(v_a_999_, 0);
v_tail_1003_ = lean_ctor_get(v_a_999_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_a_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1005_ = v_a_999_;
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_tail_1003_);
lean_inc(v_head_1002_);
lean_dec(v_a_999_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = l_Lean_mkLevelParam(v_head_1002_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_a_1000_);
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_a_1000_);
v___x_1009_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
v_a_999_ = v_tail_1003_;
v_a_1000_ = v___x_1009_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg(lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_ref_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
v_ref_1019_ = lean_ctor_get(v___y_1016_, 5);
v___x_1020_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_inc(v_ref_1019_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_ref_1019_);
lean_ctor_set(v___x_1025_, 1, v_a_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg___boxed(lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg(v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(lean_object* v_ref_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_fileName_1044_; lean_object* v_fileMap_1045_; lean_object* v_options_1046_; lean_object* v_currRecDepth_1047_; lean_object* v_maxRecDepth_1048_; lean_object* v_ref_1049_; lean_object* v_currNamespace_1050_; lean_object* v_openDecls_1051_; lean_object* v_initHeartbeats_1052_; lean_object* v_maxHeartbeats_1053_; lean_object* v_quotContext_1054_; lean_object* v_currMacroScope_1055_; uint8_t v_diag_1056_; lean_object* v_cancelTk_x3f_1057_; uint8_t v_suppressElabErrors_1058_; lean_object* v_inheritedTraceOptions_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1068_; 
v_fileName_1044_ = lean_ctor_get(v___y_1041_, 0);
v_fileMap_1045_ = lean_ctor_get(v___y_1041_, 1);
v_options_1046_ = lean_ctor_get(v___y_1041_, 2);
v_currRecDepth_1047_ = lean_ctor_get(v___y_1041_, 3);
v_maxRecDepth_1048_ = lean_ctor_get(v___y_1041_, 4);
v_ref_1049_ = lean_ctor_get(v___y_1041_, 5);
v_currNamespace_1050_ = lean_ctor_get(v___y_1041_, 6);
v_openDecls_1051_ = lean_ctor_get(v___y_1041_, 7);
v_initHeartbeats_1052_ = lean_ctor_get(v___y_1041_, 8);
v_maxHeartbeats_1053_ = lean_ctor_get(v___y_1041_, 9);
v_quotContext_1054_ = lean_ctor_get(v___y_1041_, 10);
v_currMacroScope_1055_ = lean_ctor_get(v___y_1041_, 11);
v_diag_1056_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*14);
v_cancelTk_x3f_1057_ = lean_ctor_get(v___y_1041_, 12);
v_suppressElabErrors_1058_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1059_ = lean_ctor_get(v___y_1041_, 13);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___y_1041_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1061_ = v___y_1041_;
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_inheritedTraceOptions_1059_);
lean_inc(v_cancelTk_x3f_1057_);
lean_inc(v_currMacroScope_1055_);
lean_inc(v_quotContext_1054_);
lean_inc(v_maxHeartbeats_1053_);
lean_inc(v_initHeartbeats_1052_);
lean_inc(v_openDecls_1051_);
lean_inc(v_currNamespace_1050_);
lean_inc(v_ref_1049_);
lean_inc(v_maxRecDepth_1048_);
lean_inc(v_currRecDepth_1047_);
lean_inc(v_options_1046_);
lean_inc(v_fileMap_1045_);
lean_inc(v_fileName_1044_);
lean_dec(v___y_1041_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_ref_1063_; lean_object* v___x_1065_; 
v_ref_1063_ = l_Lean_replaceRef(v_ref_1037_, v_ref_1049_);
lean_dec(v_ref_1049_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 5, v_ref_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_fileName_1044_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_fileMap_1045_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_options_1046_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_currRecDepth_1047_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_maxRecDepth_1048_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v_ref_1063_);
lean_ctor_set(v_reuseFailAlloc_1067_, 6, v_currNamespace_1050_);
lean_ctor_set(v_reuseFailAlloc_1067_, 7, v_openDecls_1051_);
lean_ctor_set(v_reuseFailAlloc_1067_, 8, v_initHeartbeats_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 9, v_maxHeartbeats_1053_);
lean_ctor_set(v_reuseFailAlloc_1067_, 10, v_quotContext_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 11, v_currMacroScope_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 12, v_cancelTk_x3f_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 13, v_inheritedTraceOptions_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1067_, sizeof(void*)*14, v_diag_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1067_, sizeof(void*)*14 + 1, v_suppressElabErrors_1058_);
v___x_1065_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg(v_msg_1038_, v___y_1039_, v___y_1040_, v___x_1065_, v___y_1042_);
lean_dec_ref(v___x_1065_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_ref_1069_, lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(v_ref_1069_, v_msg_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_ref_1069_);
return v_res_1076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__0);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
lean_ctor_set(v___x_1082_, 3, v___x_1080_);
lean_ctor_set(v___x_1082_, 4, v___x_1080_);
lean_ctor_set(v___x_1082_, 5, v___x_1080_);
lean_ctor_set(v___x_1082_, 6, v___x_1080_);
lean_ctor_set(v___x_1082_, 7, v___x_1080_);
lean_ctor_set(v___x_1082_, 8, v___x_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_unsigned_to_nat(32u);
v___x_1084_ = lean_mk_empty_array_with_capacity(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__4(void){
_start:
{
size_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1086_ = ((size_t)5ULL);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_unsigned_to_nat(32u);
v___x_1089_ = lean_mk_empty_array_with_capacity(v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__3);
v___x_1091_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___x_1089_);
lean_ctor_set(v___x_1091_, 2, v___x_1087_);
lean_ctor_set(v___x_1091_, 3, v___x_1087_);
lean_ctor_set_usize(v___x_1091_, 4, v___x_1086_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_box(1);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__4);
v___x_1094_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1);
v___x_1095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1092_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__6));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__8));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__10));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__12));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__14));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__17(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__16));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__19(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__18));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg(lean_object* v_msg_1117_, lean_object* v_declHint_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v_env_1122_; uint8_t v___x_1123_; 
v___x_1121_ = lean_st_ref_get(v___y_1119_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_Name_isAnonymous(v_declHint_1118_);
if (v___x_1123_ == 0)
{
uint8_t v_isExporting_1124_; 
v_isExporting_1124_ = lean_ctor_get_uint8(v_env_1122_, sizeof(void*)*8);
if (v_isExporting_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_msg_1117_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
lean_inc_ref(v_env_1122_);
v___x_1126_ = l_Lean_Environment_setExporting(v_env_1122_, v___x_1123_);
lean_inc(v_declHint_1118_);
lean_inc_ref(v___x_1126_);
v___x_1127_ = l_Lean_Environment_contains(v___x_1126_, v_declHint_1118_, v_isExporting_1124_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_msg_1117_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_c_1134_; lean_object* v___x_1135_; 
v___x_1129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__2);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__5);
v___x_1131_ = l_Lean_Options_empty;
v___x_1132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1126_);
lean_ctor_set(v___x_1132_, 1, v___x_1129_);
lean_ctor_set(v___x_1132_, 2, v___x_1130_);
lean_ctor_set(v___x_1132_, 3, v___x_1131_);
lean_inc(v_declHint_1118_);
v___x_1133_ = l_Lean_MessageData_ofConstName(v_declHint_1118_, v___x_1123_);
v_c_1134_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1134_, 0, v___x_1132_);
lean_ctor_set(v_c_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1122_, v_declHint_1118_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_c_1134_);
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__9);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_note(v___x_1139_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_msg_1117_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1178_; 
v_val_1143_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1145_ = v___x_1135_;
v_isShared_1146_ = v_isSharedCheck_1178_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___x_1135_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1178_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_mod_1150_; uint8_t v___x_1151_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Lean_Environment_header(v_env_1122_);
lean_dec_ref(v_env_1122_);
v___x_1149_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1148_);
v_mod_1150_ = lean_array_get(v___x_1147_, v___x_1149_, v_val_1143_);
lean_dec(v_val_1143_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = l_Lean_isPrivateName(v_declHint_1118_);
lean_dec(v_declHint_1118_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__11);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_c_1134_);
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__13);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofName(v_mod_1150_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_note(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_msg_1117_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1161_);
v___x_1163_ = v___x_1145_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__7);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_c_1134_);
v___x_1167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__17);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_MessageData_ofName(v_mod_1150_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__19);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_MessageData_note(v___x_1172_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_msg_1117_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1174_);
v___x_1176_ = v___x_1145_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1179_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_msg_1117_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___boxed(lean_object* v_msg_1180_, lean_object* v_declHint_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg(v_msg_1180_, v_declHint_1181_, v___y_1182_);
lean_dec(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15(lean_object* v_msg_1185_, lean_object* v_declHint_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v___x_1192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg(v_msg_1185_, v_declHint_1186_, v___y_1190_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = l_Lean_unknownIdentifierMessageTag;
v___x_1198_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15___boxed(lean_object* v_msg_1203_, lean_object* v_declHint_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15(v_msg_1203_, v_declHint_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg(lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v_declHint_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v_a_1220_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15(v_msg_1212_, v_declHint_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(v_ref_1211_, v_a_1220_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1222_, lean_object* v_msg_1223_, lean_object* v_declHint_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg(v_ref_1222_, v_msg_1223_, v_declHint_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v_ref_1222_);
return v_res_1230_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_ref_1237_, lean_object* v_constName_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1244_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1);
v___x_1245_ = 0;
lean_inc(v_constName_1238_);
v___x_1246_ = l_Lean_MessageData_ofConstName(v_constName_1238_, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1244_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg(v_ref_1237_, v___x_1249_, v_constName_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_ref_1251_, lean_object* v_constName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_1251_, v_constName_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_ref_1251_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(lean_object* v_constName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_ref_1265_; lean_object* v___x_1266_; 
v_ref_1265_ = lean_ctor_get(v___y_1262_, 5);
lean_inc(v_ref_1265_);
v___x_1266_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_1265_, v_constName_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v_ref_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v_env_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1280_ = lean_st_ref_get(v___y_1278_);
v_env_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc_ref(v_env_1281_);
lean_dec(v___x_1280_);
v___x_1282_ = 0;
lean_inc(v_constName_1274_);
v___x_1283_ = l_Lean_Environment_findConstVal_x3f(v_env_1281_, v_constName_1274_, v___x_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v___y_1277_);
lean_dec(v_constName_1274_);
v_val_1285_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1283_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 0);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_val_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3___boxed(lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object* v_constName_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
lean_inc(v_constName_1300_);
v___x_1306_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_levelParams_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v_levelParams_1311_ = lean_ctor_get(v_a_1307_, 1);
lean_inc(v_levelParams_1311_);
lean_dec(v_a_1307_);
v___x_1312_ = lean_box(0);
v___x_1313_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(v_levelParams_1311_, v___x_1312_);
v___x_1314_ = l_Lean_mkConst(v_constName_1300_, v___x_1313_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1314_);
v___x_1316_ = v___x_1309_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_constName_1300_);
v_a_1319_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1306_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1306_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object* v_constName_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_constName_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(lean_object* v_as_1334_, size_t v_i_1335_, size_t v_stop_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_eq(v_i_1335_, v_stop_1336_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_array_uget_borrowed(v_as_1334_, v_i_1335_);
lean_inc_ref(v___y_1340_);
lean_inc(v___x_1344_);
v___x_1345_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v___x_1344_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v_a_1346_);
v___x_1347_ = lean_infer_type(v_a_1346_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1349_ = l_Lean_Meta_isClass_x3f(v_a_1348_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v_a_1352_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v___x_1349_);
v___x_1356_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1));
v___x_1357_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_a_1350_, v___x_1356_);
lean_dec(v_a_1350_);
if (v___x_1357_ == 0)
{
lean_dec(v_a_1346_);
v_a_1352_ = v_b_1337_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1358_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
v___x_1359_ = l_Lean_MessageData_ofConst(v_a_1346_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1358_);
v___x_1362_ = lean_array_push(v_b_1337_, v___x_1361_);
v_a_1352_ = v___x_1362_;
goto v___jp_1351_;
}
v___jp_1351_:
{
size_t v___x_1353_; size_t v___x_1354_; 
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1335_, v___x_1353_);
v_i_1335_ = v___x_1354_;
v_b_1337_ = v_a_1352_;
goto _start;
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1346_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_b_1337_);
v_a_1363_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1349_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1349_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1346_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_b_1337_);
v_a_1371_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1347_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1347_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_b_1337_);
v_a_1379_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1345_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1345_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v___x_1387_; 
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_b_1337_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8___boxed(lean_object* v_as_1388_, lean_object* v_i_1389_, lean_object* v_stop_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_i_boxed_1397_; size_t v_stop_boxed_1398_; lean_object* v_res_1399_; 
v_i_boxed_1397_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_stop_boxed_1398_ = lean_unbox_usize(v_stop_1390_);
lean_dec(v_stop_1390_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_1388_, v_i_boxed_1397_, v_stop_boxed_1398_, v_b_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec_ref(v_as_1388_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object* v_as_1402_, lean_object* v_start_1403_, lean_object* v_stop_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0));
v___x_1411_ = lean_nat_dec_lt(v_start_1403_, v_stop_1404_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = lean_array_get_size(v_as_1402_);
v___x_1414_ = lean_nat_dec_le(v_stop_1404_, v___x_1413_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_lt(v_start_1403_, v___x_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1410_);
return v___x_1416_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_usize_of_nat(v_start_1403_);
v___x_1418_ = lean_usize_of_nat(v___x_1413_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_1402_, v___x_1417_, v___x_1418_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1419_;
}
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_usize_of_nat(v_start_1403_);
v___x_1421_ = lean_usize_of_nat(v_stop_1404_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_1402_, v___x_1420_, v___x_1421_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object* v_as_1423_, lean_object* v_start_1424_, lean_object* v_stop_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v_as_1423_, v_start_1424_, v_stop_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v_stop_1425_);
lean_dec(v_start_1424_);
lean_dec_ref(v_as_1423_);
return v_res_1431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__1);
v___x_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_ctor_set(v___x_1435_, 2, v___x_1434_);
lean_ctor_set(v___x_1435_, 3, v___x_1434_);
lean_ctor_set(v___x_1435_, 4, v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1436_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object* v_s_1441_, lean_object* v___f_1442_, uint8_t v___x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1493_; lean_object* v___y_1494_; uint8_t v___y_1495_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___x_1568_; lean_object* v_fileName_1569_; lean_object* v_fileMap_1570_; lean_object* v_options_1571_; lean_object* v_currRecDepth_1572_; lean_object* v_ref_1573_; lean_object* v_currNamespace_1574_; lean_object* v_openDecls_1575_; lean_object* v_initHeartbeats_1576_; lean_object* v_maxHeartbeats_1577_; lean_object* v_quotContext_1578_; lean_object* v_currMacroScope_1579_; lean_object* v_cancelTk_x3f_1580_; uint8_t v_suppressElabErrors_1581_; lean_object* v_inheritedTraceOptions_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1659_; 
v___x_1568_ = lean_st_ref_get(v___y_1447_);
v_fileName_1569_ = lean_ctor_get(v___y_1446_, 0);
v_fileMap_1570_ = lean_ctor_get(v___y_1446_, 1);
v_options_1571_ = lean_ctor_get(v___y_1446_, 2);
v_currRecDepth_1572_ = lean_ctor_get(v___y_1446_, 3);
v_ref_1573_ = lean_ctor_get(v___y_1446_, 5);
v_currNamespace_1574_ = lean_ctor_get(v___y_1446_, 6);
v_openDecls_1575_ = lean_ctor_get(v___y_1446_, 7);
v_initHeartbeats_1576_ = lean_ctor_get(v___y_1446_, 8);
v_maxHeartbeats_1577_ = lean_ctor_get(v___y_1446_, 9);
v_quotContext_1578_ = lean_ctor_get(v___y_1446_, 10);
v_currMacroScope_1579_ = lean_ctor_get(v___y_1446_, 11);
v_cancelTk_x3f_1580_ = lean_ctor_get(v___y_1446_, 12);
v_suppressElabErrors_1581_ = lean_ctor_get_uint8(v___y_1446_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1582_ = lean_ctor_get(v___y_1446_, 13);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___y_1446_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v___y_1446_, 4);
lean_dec(v_unused_1660_);
v___x_1584_ = v___y_1446_;
v_isShared_1585_ = v_isSharedCheck_1659_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_inheritedTraceOptions_1582_);
lean_inc(v_cancelTk_x3f_1580_);
lean_inc(v_currMacroScope_1579_);
lean_inc(v_quotContext_1578_);
lean_inc(v_maxHeartbeats_1577_);
lean_inc(v_initHeartbeats_1576_);
lean_inc(v_openDecls_1575_);
lean_inc(v_currNamespace_1574_);
lean_inc(v_ref_1573_);
lean_inc(v_currRecDepth_1572_);
lean_inc(v_options_1571_);
lean_inc(v_fileMap_1570_);
lean_inc(v_fileName_1569_);
lean_dec(v___y_1446_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1659_;
goto v_resetjp_1583_;
}
v___jp_1449_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_array_get_size(v___y_1454_);
v___x_1456_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v___y_1454_, v___y_1451_, v___x_1455_, v___y_1444_, v___y_1445_, v___y_1450_, v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1454_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1453_);
lean_ctor_set(v___x_1461_, 1, v_a_1457_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec_ref(v___y_1453_);
v_a_1466_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1456_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1456_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
v___jp_1474_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v___y_1478_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
v___y_1450_ = v___y_1476_;
v___y_1451_ = v___y_1475_;
v___y_1452_ = v___y_1477_;
v___y_1453_ = v___y_1479_;
v___y_1454_ = v___x_1482_;
goto v___jp_1449_;
}
v___jp_1483_:
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_nat_dec_le(v___y_1490_, v___y_1489_);
if (v___x_1491_ == 0)
{
lean_dec(v___y_1489_);
lean_inc(v___y_1490_);
v___y_1475_ = v___y_1485_;
v___y_1476_ = v___y_1484_;
v___y_1477_ = v___y_1486_;
v___y_1478_ = v___y_1487_;
v___y_1479_ = v___y_1488_;
v___y_1480_ = v___y_1490_;
v___y_1481_ = v___y_1490_;
goto v___jp_1474_;
}
else
{
v___y_1475_ = v___y_1485_;
v___y_1476_ = v___y_1484_;
v___y_1477_ = v___y_1486_;
v___y_1478_ = v___y_1487_;
v___y_1479_ = v___y_1488_;
v___y_1480_ = v___y_1490_;
v___y_1481_ = v___y_1489_;
goto v___jp_1474_;
}
}
v___jp_1492_:
{
lean_object* v___x_1496_; uint8_t v_foApprox_1497_; uint8_t v_ctxApprox_1498_; uint8_t v_quasiPatternApprox_1499_; uint8_t v_constApprox_1500_; uint8_t v_isDefEqStuckEx_1501_; uint8_t v_unificationHints_1502_; uint8_t v_proofIrrelevance_1503_; uint8_t v_assignSyntheticOpaque_1504_; uint8_t v_offsetCnstrs_1505_; uint8_t v_etaStruct_1506_; uint8_t v_univApprox_1507_; uint8_t v_iota_1508_; uint8_t v_beta_1509_; uint8_t v_proj_1510_; uint8_t v_zeta_1511_; uint8_t v_zetaDelta_1512_; uint8_t v_zetaUnused_1513_; uint8_t v_zetaHave_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1560_; 
v___x_1496_ = l_Lean_Meta_Context_config(v___y_1444_);
v_foApprox_1497_ = lean_ctor_get_uint8(v___x_1496_, 0);
v_ctxApprox_1498_ = lean_ctor_get_uint8(v___x_1496_, 1);
v_quasiPatternApprox_1499_ = lean_ctor_get_uint8(v___x_1496_, 2);
v_constApprox_1500_ = lean_ctor_get_uint8(v___x_1496_, 3);
v_isDefEqStuckEx_1501_ = lean_ctor_get_uint8(v___x_1496_, 4);
v_unificationHints_1502_ = lean_ctor_get_uint8(v___x_1496_, 5);
v_proofIrrelevance_1503_ = lean_ctor_get_uint8(v___x_1496_, 6);
v_assignSyntheticOpaque_1504_ = lean_ctor_get_uint8(v___x_1496_, 7);
v_offsetCnstrs_1505_ = lean_ctor_get_uint8(v___x_1496_, 8);
v_etaStruct_1506_ = lean_ctor_get_uint8(v___x_1496_, 10);
v_univApprox_1507_ = lean_ctor_get_uint8(v___x_1496_, 11);
v_iota_1508_ = lean_ctor_get_uint8(v___x_1496_, 12);
v_beta_1509_ = lean_ctor_get_uint8(v___x_1496_, 13);
v_proj_1510_ = lean_ctor_get_uint8(v___x_1496_, 14);
v_zeta_1511_ = lean_ctor_get_uint8(v___x_1496_, 15);
v_zetaDelta_1512_ = lean_ctor_get_uint8(v___x_1496_, 16);
v_zetaUnused_1513_ = lean_ctor_get_uint8(v___x_1496_, 17);
v_zetaHave_1514_ = lean_ctor_get_uint8(v___x_1496_, 18);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1516_ = v___x_1496_;
v_isShared_1517_ = v_isSharedCheck_1560_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v___x_1496_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1560_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
uint8_t v_trackZetaDelta_1518_; lean_object* v_zetaDeltaSet_1519_; lean_object* v_lctx_1520_; lean_object* v_localInstances_1521_; lean_object* v_defEqCtx_x3f_1522_; lean_object* v_synthPendingDepth_1523_; lean_object* v_canUnfold_x3f_1524_; uint8_t v_univApprox_1525_; uint8_t v_inTypeClassResolution_1526_; uint8_t v_cacheInferType_1527_; lean_object* v_config_1529_; 
v_trackZetaDelta_1518_ = lean_ctor_get_uint8(v___y_1444_, sizeof(void*)*7);
v_zetaDeltaSet_1519_ = lean_ctor_get(v___y_1444_, 1);
v_lctx_1520_ = lean_ctor_get(v___y_1444_, 2);
v_localInstances_1521_ = lean_ctor_get(v___y_1444_, 3);
v_defEqCtx_x3f_1522_ = lean_ctor_get(v___y_1444_, 4);
v_synthPendingDepth_1523_ = lean_ctor_get(v___y_1444_, 5);
v_canUnfold_x3f_1524_ = lean_ctor_get(v___y_1444_, 6);
v_univApprox_1525_ = lean_ctor_get_uint8(v___y_1444_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1526_ = lean_ctor_get_uint8(v___y_1444_, sizeof(void*)*7 + 2);
v_cacheInferType_1527_ = lean_ctor_get_uint8(v___y_1444_, sizeof(void*)*7 + 3);
if (v_isShared_1517_ == 0)
{
v_config_1529_ = v___x_1516_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 0, v_foApprox_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 1, v_ctxApprox_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 2, v_quasiPatternApprox_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 3, v_constApprox_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 4, v_isDefEqStuckEx_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 5, v_unificationHints_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 6, v_proofIrrelevance_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 7, v_assignSyntheticOpaque_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 8, v_offsetCnstrs_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 10, v_etaStruct_1506_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 11, v_univApprox_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 12, v_iota_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 13, v_beta_1509_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 14, v_proj_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 15, v_zeta_1511_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 16, v_zetaDelta_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 17, v_zetaUnused_1513_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, 18, v_zetaHave_1514_);
v_config_1529_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
uint64_t v___x_1530_; uint64_t v___x_1531_; uint64_t v___x_1532_; uint64_t v___x_1533_; uint64_t v___x_1534_; uint64_t v_key_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_ctor_set_uint8(v_config_1529_, 9, v___y_1495_);
v___x_1530_ = l_Lean_Meta_Context_configKey(v___y_1444_);
v___x_1531_ = 2ULL;
v___x_1532_ = lean_uint64_shift_right(v___x_1530_, v___x_1531_);
v___x_1533_ = lean_uint64_shift_left(v___x_1532_, v___x_1531_);
v___x_1534_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1495_);
v_key_1535_ = lean_uint64_lor(v___x_1533_, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1536_, 0, v_config_1529_);
lean_ctor_set_uint64(v___x_1536_, sizeof(void*)*1, v_key_1535_);
lean_inc(v_canUnfold_x3f_1524_);
lean_inc(v_synthPendingDepth_1523_);
lean_inc(v_defEqCtx_x3f_1522_);
lean_inc_ref(v_localInstances_1521_);
lean_inc_ref(v_lctx_1520_);
lean_inc(v_zetaDeltaSet_1519_);
v___x_1537_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v_zetaDeltaSet_1519_);
lean_ctor_set(v___x_1537_, 2, v_lctx_1520_);
lean_ctor_set(v___x_1537_, 3, v_localInstances_1521_);
lean_ctor_set(v___x_1537_, 4, v_defEqCtx_x3f_1522_);
lean_ctor_set(v___x_1537_, 5, v_synthPendingDepth_1523_);
lean_ctor_set(v___x_1537_, 6, v_canUnfold_x3f_1524_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7, v_trackZetaDelta_1518_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7 + 1, v_univApprox_1525_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1526_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*7 + 3, v_cacheInferType_1527_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1445_);
v___x_1538_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1441_, v___x_1537_, v___y_1445_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; lean_object* v_diag_1541_; lean_object* v_unfoldCounter_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = lean_st_ref_get(v___y_1445_);
v_diag_1541_ = lean_ctor_get(v___x_1540_, 4);
lean_inc_ref(v_diag_1541_);
lean_dec(v___x_1540_);
v_unfoldCounter_1542_ = lean_ctor_get(v_diag_1541_, 0);
lean_inc_ref(v_unfoldCounter_1542_);
lean_dec_ref(v_diag_1541_);
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_1545_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_unfoldCounter_1542_, v___f_1442_, v___x_1544_);
lean_dec_ref(v_unfoldCounter_1542_);
v___x_1546_ = lean_array_get_size(v___x_1545_);
v___x_1547_ = lean_nat_dec_eq(v___x_1546_, v___x_1543_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_nat_sub(v___x_1546_, v___x_1548_);
v___x_1550_ = lean_nat_dec_le(v___x_1543_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_inc(v___x_1549_);
v___y_1484_ = v___y_1493_;
v___y_1485_ = v___x_1543_;
v___y_1486_ = v___y_1494_;
v___y_1487_ = v___x_1545_;
v___y_1488_ = v_a_1539_;
v___y_1489_ = v___x_1549_;
v___y_1490_ = v___x_1549_;
goto v___jp_1483_;
}
else
{
v___y_1484_ = v___y_1493_;
v___y_1485_ = v___x_1543_;
v___y_1486_ = v___y_1494_;
v___y_1487_ = v___x_1545_;
v___y_1488_ = v_a_1539_;
v___y_1489_ = v___x_1549_;
v___y_1490_ = v___x_1543_;
goto v___jp_1483_;
}
}
else
{
v___y_1450_ = v___y_1493_;
v___y_1451_ = v___x_1543_;
v___y_1452_ = v___y_1494_;
v___y_1453_ = v_a_1539_;
v___y_1454_ = v___x_1545_;
goto v___jp_1449_;
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec_ref(v___f_1442_);
v_a_1551_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1538_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1538_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
}
v___jp_1561_:
{
lean_object* v___x_1564_; uint8_t v_transparency_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1564_ = l_Lean_Meta_Context_config(v___y_1444_);
v_transparency_1565_ = lean_ctor_get_uint8(v___x_1564_, 9);
lean_dec_ref(v___x_1564_);
v___x_1566_ = 1;
v___x_1567_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
v___y_1493_ = v___y_1562_;
v___y_1494_ = v___y_1563_;
v___y_1495_ = v_transparency_1565_;
goto v___jp_1492_;
}
else
{
v___y_1493_ = v___y_1562_;
v___y_1494_ = v___y_1563_;
v___y_1495_ = v___x_1566_;
goto v___jp_1492_;
}
}
v_resetjp_1583_:
{
lean_object* v_env_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v_fileName_1591_; lean_object* v_fileMap_1592_; lean_object* v_currRecDepth_1593_; lean_object* v_ref_1594_; lean_object* v_currNamespace_1595_; lean_object* v_openDecls_1596_; lean_object* v_initHeartbeats_1597_; lean_object* v_maxHeartbeats_1598_; lean_object* v_quotContext_1599_; lean_object* v_currMacroScope_1600_; lean_object* v_cancelTk_x3f_1601_; uint8_t v_suppressElabErrors_1602_; lean_object* v_inheritedTraceOptions_1603_; lean_object* v___y_1604_; uint8_t v___y_1637_; uint8_t v___x_1658_; 
v_env_1586_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_ref(v_env_1586_);
lean_dec(v___x_1568_);
v___x_1587_ = l_Lean_diagnostics;
v___x_1588_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_1571_, v___x_1587_, v___x_1443_);
v___x_1589_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_1588_, v___x_1587_);
v___x_1658_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1586_);
lean_dec_ref(v_env_1586_);
if (v___x_1658_ == 0)
{
if (v___x_1589_ == 0)
{
v_fileName_1591_ = v_fileName_1569_;
v_fileMap_1592_ = v_fileMap_1570_;
v_currRecDepth_1593_ = v_currRecDepth_1572_;
v_ref_1594_ = v_ref_1573_;
v_currNamespace_1595_ = v_currNamespace_1574_;
v_openDecls_1596_ = v_openDecls_1575_;
v_initHeartbeats_1597_ = v_initHeartbeats_1576_;
v_maxHeartbeats_1598_ = v_maxHeartbeats_1577_;
v_quotContext_1599_ = v_quotContext_1578_;
v_currMacroScope_1600_ = v_currMacroScope_1579_;
v_cancelTk_x3f_1601_ = v_cancelTk_x3f_1580_;
v_suppressElabErrors_1602_ = v_suppressElabErrors_1581_;
v_inheritedTraceOptions_1603_ = v_inheritedTraceOptions_1582_;
v___y_1604_ = v___y_1447_;
goto v___jp_1590_;
}
else
{
v___y_1637_ = v___x_1658_;
goto v___jp_1636_;
}
}
else
{
v___y_1637_ = v___x_1589_;
goto v___jp_1636_;
}
v___jp_1590_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1605_ = l_Lean_maxRecDepth;
v___x_1606_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_1588_, v___x_1605_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 13, v_inheritedTraceOptions_1603_);
lean_ctor_set(v___x_1584_, 12, v_cancelTk_x3f_1601_);
lean_ctor_set(v___x_1584_, 11, v_currMacroScope_1600_);
lean_ctor_set(v___x_1584_, 10, v_quotContext_1599_);
lean_ctor_set(v___x_1584_, 9, v_maxHeartbeats_1598_);
lean_ctor_set(v___x_1584_, 8, v_initHeartbeats_1597_);
lean_ctor_set(v___x_1584_, 7, v_openDecls_1596_);
lean_ctor_set(v___x_1584_, 6, v_currNamespace_1595_);
lean_ctor_set(v___x_1584_, 5, v_ref_1594_);
lean_ctor_set(v___x_1584_, 4, v___x_1606_);
lean_ctor_set(v___x_1584_, 3, v_currRecDepth_1593_);
lean_ctor_set(v___x_1584_, 2, v___x_1588_);
lean_ctor_set(v___x_1584_, 1, v_fileMap_1592_);
lean_ctor_set(v___x_1584_, 0, v_fileName_1591_);
v___x_1608_ = v___x_1584_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_fileName_1591_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_fileMap_1592_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_currRecDepth_1593_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1635_, 5, v_ref_1594_);
lean_ctor_set(v_reuseFailAlloc_1635_, 6, v_currNamespace_1595_);
lean_ctor_set(v_reuseFailAlloc_1635_, 7, v_openDecls_1596_);
lean_ctor_set(v_reuseFailAlloc_1635_, 8, v_initHeartbeats_1597_);
lean_ctor_set(v_reuseFailAlloc_1635_, 9, v_maxHeartbeats_1598_);
lean_ctor_set(v_reuseFailAlloc_1635_, 10, v_quotContext_1599_);
lean_ctor_set(v_reuseFailAlloc_1635_, 11, v_currMacroScope_1600_);
lean_ctor_set(v_reuseFailAlloc_1635_, 12, v_cancelTk_x3f_1601_);
lean_ctor_set(v_reuseFailAlloc_1635_, 13, v_inheritedTraceOptions_1603_);
v___x_1608_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; 
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*14, v___x_1589_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*14 + 1, v_suppressElabErrors_1602_);
v___x_1609_ = l_Lean_isDiagnosticsEnabled___redArg(v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; uint8_t v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = lean_unbox(v_a_1610_);
lean_dec(v_a_1610_);
if (v___x_1611_ == 0)
{
v___y_1562_ = v___x_1608_;
v___y_1563_ = v___y_1604_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1612_; lean_object* v_mctx_1613_; lean_object* v_cache_1614_; lean_object* v_zetaDeltaFVarIds_1615_; lean_object* v_postponed_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1625_; 
v___x_1612_ = lean_st_ref_take(v___y_1445_);
v_mctx_1613_ = lean_ctor_get(v___x_1612_, 0);
v_cache_1614_ = lean_ctor_get(v___x_1612_, 1);
v_zetaDeltaFVarIds_1615_ = lean_ctor_get(v___x_1612_, 2);
v_postponed_1616_ = lean_ctor_get(v___x_1612_, 3);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v___x_1612_, 4);
lean_dec(v_unused_1626_);
v___x_1618_ = v___x_1612_;
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_postponed_1616_);
lean_inc(v_zetaDeltaFVarIds_1615_);
lean_inc(v_cache_1614_);
lean_inc(v_mctx_1613_);
lean_dec(v___x_1612_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v___x_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_mctx_1613_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_cache_1614_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_zetaDeltaFVarIds_1615_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_postponed_1616_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_st_ref_set(v___y_1445_, v___x_1622_);
v___y_1562_ = v___x_1608_;
v___y_1563_ = v___y_1604_;
goto v___jp_1561_;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v___x_1608_);
lean_dec(v___y_1604_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec_ref(v___f_1442_);
lean_dec_ref(v_s_1441_);
v_a_1627_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1609_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1609_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
v___jp_1636_:
{
if (v___y_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v_env_1639_; lean_object* v_nextMacroScope_1640_; lean_object* v_ngen_1641_; lean_object* v_auxDeclNGen_1642_; lean_object* v_traceState_1643_; lean_object* v_messages_1644_; lean_object* v_infoState_1645_; lean_object* v_snapshotTasks_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1656_; 
v___x_1638_ = lean_st_ref_take(v___y_1447_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
v_nextMacroScope_1640_ = lean_ctor_get(v___x_1638_, 1);
v_ngen_1641_ = lean_ctor_get(v___x_1638_, 2);
v_auxDeclNGen_1642_ = lean_ctor_get(v___x_1638_, 3);
v_traceState_1643_ = lean_ctor_get(v___x_1638_, 4);
v_messages_1644_ = lean_ctor_get(v___x_1638_, 6);
v_infoState_1645_ = lean_ctor_get(v___x_1638_, 7);
v_snapshotTasks_1646_ = lean_ctor_get(v___x_1638_, 8);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v___x_1638_, 5);
lean_dec(v_unused_1657_);
v___x_1648_ = v___x_1638_;
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snapshotTasks_1646_);
lean_inc(v_infoState_1645_);
lean_inc(v_messages_1644_);
lean_inc(v_traceState_1643_);
lean_inc(v_auxDeclNGen_1642_);
lean_inc(v_ngen_1641_);
lean_inc(v_nextMacroScope_1640_);
lean_inc(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1650_ = l_Lean_Kernel_enableDiag(v_env_1639_, v___x_1589_);
v___x_1651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 5, v___x_1651_);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_nextMacroScope_1640_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_ngen_1641_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_auxDeclNGen_1642_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_traceState_1643_);
lean_ctor_set(v_reuseFailAlloc_1655_, 5, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1655_, 6, v_messages_1644_);
lean_ctor_set(v_reuseFailAlloc_1655_, 7, v_infoState_1645_);
lean_ctor_set(v_reuseFailAlloc_1655_, 8, v_snapshotTasks_1646_);
v___x_1653_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_st_ref_set(v___y_1447_, v___x_1653_);
v_fileName_1591_ = v_fileName_1569_;
v_fileMap_1592_ = v_fileMap_1570_;
v_currRecDepth_1593_ = v_currRecDepth_1572_;
v_ref_1594_ = v_ref_1573_;
v_currNamespace_1595_ = v_currNamespace_1574_;
v_openDecls_1596_ = v_openDecls_1575_;
v_initHeartbeats_1597_ = v_initHeartbeats_1576_;
v_maxHeartbeats_1598_ = v_maxHeartbeats_1577_;
v_quotContext_1599_ = v_quotContext_1578_;
v_currMacroScope_1600_ = v_currMacroScope_1579_;
v_cancelTk_x3f_1601_ = v_cancelTk_x3f_1580_;
v_suppressElabErrors_1602_ = v_suppressElabErrors_1581_;
v_inheritedTraceOptions_1603_ = v_inheritedTraceOptions_1582_;
v___y_1604_ = v___y_1447_;
goto v___jp_1590_;
}
}
}
else
{
v_fileName_1591_ = v_fileName_1569_;
v_fileMap_1592_ = v_fileMap_1570_;
v_currRecDepth_1593_ = v_currRecDepth_1572_;
v_ref_1594_ = v_ref_1573_;
v_currNamespace_1595_ = v_currNamespace_1574_;
v_openDecls_1596_ = v_openDecls_1575_;
v_initHeartbeats_1597_ = v_initHeartbeats_1576_;
v_maxHeartbeats_1598_ = v_maxHeartbeats_1577_;
v_quotContext_1599_ = v_quotContext_1578_;
v_currMacroScope_1600_ = v_currMacroScope_1579_;
v_cancelTk_x3f_1601_ = v_cancelTk_x3f_1580_;
v_suppressElabErrors_1602_ = v_suppressElabErrors_1581_;
v_inheritedTraceOptions_1603_ = v_inheritedTraceOptions_1582_;
v___y_1604_ = v___y_1447_;
goto v___jp_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object* v_s_1661_, lean_object* v___f_1662_, lean_object* v___x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v___x_13545__boxed_1669_; lean_object* v_res_1670_; 
v___x_13545__boxed_1669_ = lean_unbox(v___x_1663_);
v_res_1670_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(v_s_1661_, v___f_1662_, v___x_13545__boxed_1669_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v_res_1670_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20));
v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
return v___x_1704_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22));
v___x_1707_ = l_Lean_stringToMessageData(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42));
v___x_1738_ = l_Lean_stringToMessageData(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44));
v___x_1741_ = l_Lean_stringToMessageData(v___x_1740_);
return v___x_1741_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48));
v___x_1746_ = l_Lean_stringToMessageData(v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* v_tacticName_1750_, lean_object* v_expectedType_1751_, lean_object* v_s_1752_, lean_object* v_r_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5));
v___x_1760_ = l_Lean_Expr_isAppOf(v_r_1753_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___f_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; 
v___f_1761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0));
v___x_1762_ = 1;
v___x_1763_ = lean_box(v___x_1762_);
lean_inc_ref(v_s_1752_);
v___f_1764_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1764_, 0, v_s_1752_);
lean_closure_set(v___f_1764_, 1, v___f_1761_);
lean_closure_set(v___f_1764_, 2, v___x_1763_);
v___x_1765_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v___f_1764_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1897_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1897_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1897_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v_fst_1805_; lean_object* v_snd_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1896_; 
v_fst_1805_ = lean_ctor_get(v_a_1766_, 0);
v_snd_1806_ = lean_ctor_get(v_a_1766_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_a_1766_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1808_ = v_a_1766_;
v_isShared_1809_ = v_isSharedCheck_1896_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_snd_1806_);
lean_inc(v_fst_1805_);
lean_dec(v_a_1766_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1896_;
goto v_resetjp_1807_;
}
v___jp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1774_ = l_Lean_MessageData_ofName(v_tacticName_1750_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_indentExpr(v_expectedType_1751_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0));
v___x_1783_ = l_Lean_MessageData_ofConstName(v___x_1782_, v___x_1760_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1781_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_indentExpr(v_s_1752_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3));
v___x_1792_ = l_Lean_MessageData_ofConstName(v___x_1791_, v___x_1760_);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1790_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = l_Lean_MessageData_ofConstName(v___x_1759_, v___x_1760_);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___y_1771_);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___y_1772_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1801_);
v___x_1803_ = v___x_1768_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
v_resetjp_1807_:
{
lean_object* v___y_1811_; lean_object* v___y_1863_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = lean_array_get_size(v_snd_1806_);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_nat_dec_eq(v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_nat_dec_eq(v___x_1881_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46));
v___y_1863_ = v___x_1886_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47));
v___y_1863_ = v___x_1887_;
goto v___jp_1862_;
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_snd_1806_);
v___x_1888_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49);
v___x_1889_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0));
v___x_1890_ = l_Lean_MessageData_ofConstName(v___x_1889_, v___x_1760_);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
lean_inc(v_fst_1805_);
v___x_1894_ = l_Lean_indentExpr(v_fst_1805_);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___y_1811_ = v___x_1895_;
goto v___jp_1810_;
}
v___jp_1810_:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14));
v___x_1813_ = l_Lean_Expr_isAppOf(v_fst_1805_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17));
v___x_1815_ = l_Lean_Expr_isAppOf(v_fst_1805_, v___x_1814_);
lean_dec(v_fst_1805_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_del_object(v___x_1808_);
v___x_1816_ = l_Lean_MessageData_nil;
v___y_1771_ = v___y_1811_;
v___y_1772_ = v___x_1816_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1817_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19);
v___x_1818_ = l_Lean_MessageData_ofConstName(v___x_1814_, v___x_1760_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 7);
lean_ctor_set(v___x_1808_, 1, v___x_1818_);
lean_ctor_set(v___x_1808_, 0, v___x_1817_);
v___x_1820_ = v___x_1808_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0));
v___x_1824_ = l_Lean_MessageData_ofConstName(v___x_1823_, v___x_1760_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1822_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
lean_inc(v_tacticName_1750_);
v___x_1828_ = l_Lean_MessageData_ofName(v_tacticName_1750_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27));
v___x_1833_ = l_Lean_MessageData_ofConstName(v___x_1832_, v___x_1760_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1831_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg___closed__15);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_MessageData_hint_x27(v___x_1836_);
v___y_1771_ = v___y_1811_;
v___y_1772_ = v___x_1837_;
goto v___jp_1770_;
}
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec(v_fst_1805_);
v___x_1839_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29);
v___x_1840_ = l_Lean_MessageData_ofConstName(v___x_1812_, v___x_1760_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 7);
lean_ctor_set(v___x_1808_, 1, v___x_1840_);
lean_ctor_set(v___x_1808_, 0, v___x_1839_);
v___x_1842_ = v___x_1808_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1843_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0));
v___x_1846_ = l_Lean_MessageData_ofConstName(v___x_1845_, v___x_1760_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1844_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35));
v___x_1851_ = l_Lean_MessageData_ofConstName(v___x_1850_, v___x_1760_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1849_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37));
v___x_1856_ = l_Lean_MessageData_ofConstName(v___x_1855_, v___x_1760_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_MessageData_hint_x27(v___x_1859_);
v___y_1771_ = v___y_1811_;
v___y_1772_ = v___x_1860_;
goto v___jp_1770_;
}
}
}
v___jp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1864_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41);
v___x_1865_ = l_Lean_stringToMessageData(v___y_1863_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_array_to_list(v_snd_1806_);
v___x_1870_ = l_Lean_MessageData_andList(v___x_1869_);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1868_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0));
v___x_1875_ = l_Lean_MessageData_ofConstName(v___x_1874_, v___x_1760_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
lean_inc(v_fst_1805_);
v___x_1879_ = l_Lean_indentExpr(v_fst_1805_);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___y_1811_ = v___x_1880_;
goto v___jp_1810_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v_s_1752_);
lean_dec_ref(v_expectedType_1751_);
lean_dec(v_tacticName_1750_);
v_a_1898_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1765_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1765_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec_ref(v_s_1752_);
v___x_1906_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1907_ = l_Lean_MessageData_ofName(v_tacticName_1750_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l_Lean_indentExpr(v_expectedType_1751_);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object* v_tacticName_1916_, lean_object* v_expectedType_1917_, lean_object* v_s_1918_, lean_object* v_r_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_1916_, v_expectedType_1917_, v_s_1918_, v_r_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec_ref(v_r_1919_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object* v_00_u03c3_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_map_1928_, lean_object* v_f_1929_, lean_object* v_init_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_1928_, v_f_1929_, v_init_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object* v_00_u03c3_1932_, lean_object* v_00_u03b2_1933_, lean_object* v_map_1934_, lean_object* v_f_1935_, lean_object* v_init_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_00_u03c3_1932_, v_00_u03b2_1933_, v_map_1934_, v_f_1935_, v_init_1936_);
lean_dec_ref(v_map_1934_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object* v_n_1938_, lean_object* v_as_1939_, lean_object* v_lo_1940_, lean_object* v_hi_1941_, lean_object* v_w_1942_, lean_object* v_hlo_1943_, lean_object* v_hhi_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_as_1939_, v_lo_1940_, v_hi_1941_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object* v_n_1946_, lean_object* v_as_1947_, lean_object* v_lo_1948_, lean_object* v_hi_1949_, lean_object* v_w_1950_, lean_object* v_hlo_1951_, lean_object* v_hhi_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v_n_1946_, v_as_1947_, v_lo_1948_, v_hi_1949_, v_w_1950_, v_hlo_1951_, v_hhi_1952_);
lean_dec(v_hi_1949_);
lean_dec(v_n_1946_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(lean_object* v_map_1954_, lean_object* v_f_1955_, lean_object* v_init_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_1955_, v_map_1954_, v_init_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg___boxed(lean_object* v_map_1958_, lean_object* v_f_1959_, lean_object* v_init_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(v_map_1958_, v_f_1959_, v_init_1960_);
lean_dec_ref(v_map_1958_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(lean_object* v_00_u03c3_1962_, lean_object* v_00_u03b2_1963_, lean_object* v_map_1964_, lean_object* v_f_1965_, lean_object* v_init_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_1965_, v_map_1964_, v_init_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1968_, lean_object* v_00_u03b2_1969_, lean_object* v_map_1970_, lean_object* v_f_1971_, lean_object* v_init_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(v_00_u03c3_1968_, v_00_u03b2_1969_, v_map_1970_, v_f_1971_, v_init_1972_);
lean_dec_ref(v_map_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1974_, lean_object* v_constName_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1982_, lean_object* v_constName_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(v_00_u03b1_1982_, v_constName_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(lean_object* v_00_u03c3_1990_, lean_object* v_00_u03b1_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_f_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_1993_, v_x_1994_, v_x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03c3_1997_, lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_f_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(v_00_u03c3_1997_, v_00_u03b1_1998_, v_00_u03b2_1999_, v_f_2000_, v_x_2001_, v_x_2002_);
lean_dec_ref(v_x_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b1_2004_, lean_object* v_ref_2005_, lean_object* v_constName_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_2005_, v_constName_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2013_, lean_object* v_ref_2014_, lean_object* v_constName_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(v_00_u03b1_2013_, v_ref_2014_, v_constName_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v_ref_2014_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_00_u03c3_2024_, lean_object* v_f_2025_, lean_object* v_as_2026_, size_t v_i_2027_, size_t v_stop_2028_, lean_object* v_b_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_2025_, v_as_2026_, v_i_2027_, v_stop_2028_, v_b_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2031_, lean_object* v_00_u03b2_2032_, lean_object* v_00_u03c3_2033_, lean_object* v_f_2034_, lean_object* v_as_2035_, lean_object* v_i_2036_, lean_object* v_stop_2037_, lean_object* v_b_2038_){
_start:
{
size_t v_i_boxed_2039_; size_t v_stop_boxed_2040_; lean_object* v_res_2041_; 
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_stop_boxed_2040_ = lean_unbox_usize(v_stop_2037_);
lean_dec(v_stop_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(v_00_u03b1_2031_, v_00_u03b2_2032_, v_00_u03c3_2033_, v_f_2034_, v_as_2035_, v_i_boxed_2039_, v_stop_boxed_2040_, v_b_2038_);
lean_dec_ref(v_as_2035_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(lean_object* v_00_u03c3_2042_, lean_object* v_00_u03b1_2043_, lean_object* v_00_u03b2_2044_, lean_object* v_f_2045_, lean_object* v_keys_2046_, lean_object* v_vals_2047_, lean_object* v_heq_2048_, lean_object* v_i_2049_, lean_object* v_acc_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_2045_, v_keys_2046_, v_vals_2047_, v_i_2049_, v_acc_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___boxed(lean_object* v_00_u03c3_2052_, lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_f_2055_, lean_object* v_keys_2056_, lean_object* v_vals_2057_, lean_object* v_heq_2058_, lean_object* v_i_2059_, lean_object* v_acc_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(v_00_u03c3_2052_, v_00_u03b1_2053_, v_00_u03b2_2054_, v_f_2055_, v_keys_2056_, v_vals_2057_, v_heq_2058_, v_i_2059_, v_acc_2060_);
lean_dec_ref(v_vals_2057_);
lean_dec_ref(v_keys_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13(lean_object* v_00_u03b1_2062_, lean_object* v_ref_2063_, lean_object* v_msg_2064_, lean_object* v_declHint_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___redArg(v_ref_2063_, v_msg_2064_, v_declHint_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_ref_2073_, lean_object* v_msg_2074_, lean_object* v_declHint_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13(v_00_u03b1_2072_, v_ref_2073_, v_msg_2074_, v_declHint_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v_ref_2073_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18(lean_object* v_msg_2082_, lean_object* v_declHint_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___redArg(v_msg_2082_, v_declHint_2083_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18___boxed(lean_object* v_msg_2090_, lean_object* v_declHint_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__15_spec__18(v_msg_2090_, v_declHint_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16(lean_object* v_00_u03b1_2098_, lean_object* v_ref_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___redArg(v_ref_2099_, v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b1_2107_, lean_object* v_ref_2108_, lean_object* v_msg_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16(v_00_u03b1_2107_, v_ref_2108_, v_msg_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v_ref_2108_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20(lean_object* v_00_u03b1_2116_, lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___redArg(v_msg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_msg_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__13_spec__16_spec__20(v_00_u03b1_2124_, v_msg_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object* v_tacticName_2132_, lean_object* v_expectedType_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; 
lean_inc(v_a_2137_);
lean_inc_ref(v_a_2136_);
lean_inc(v_a_2135_);
lean_inc_ref(v_a_2134_);
lean_inc_ref(v_expectedType_2133_);
v___x_2139_ = l_Lean_Meta_mkDecideProof(v_expectedType_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; uint8_t v_transparency_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___y_2146_; uint8_t v___x_2207_; uint8_t v___x_2208_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = l_Lean_Meta_Context_config(v_a_2134_);
v_transparency_2142_ = lean_ctor_get_uint8(v___x_2141_, 9);
v___x_2143_ = l_Lean_Expr_appFn_x21(v_a_2140_);
v___x_2144_ = l_Lean_Expr_appArg_x21(v___x_2143_);
lean_dec_ref(v___x_2143_);
v___x_2207_ = 1;
v___x_2208_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2142_, v___x_2207_);
if (v___x_2208_ == 0)
{
v___y_2146_ = v_transparency_2142_;
goto v___jp_2145_;
}
else
{
v___y_2146_ = v___x_2207_;
goto v___jp_2145_;
}
v___jp_2145_:
{
uint8_t v_foApprox_2147_; uint8_t v_ctxApprox_2148_; uint8_t v_quasiPatternApprox_2149_; uint8_t v_constApprox_2150_; uint8_t v_isDefEqStuckEx_2151_; uint8_t v_unificationHints_2152_; uint8_t v_proofIrrelevance_2153_; uint8_t v_assignSyntheticOpaque_2154_; uint8_t v_offsetCnstrs_2155_; uint8_t v_etaStruct_2156_; uint8_t v_univApprox_2157_; uint8_t v_iota_2158_; uint8_t v_beta_2159_; uint8_t v_proj_2160_; uint8_t v_zeta_2161_; uint8_t v_zetaDelta_2162_; uint8_t v_zetaUnused_2163_; uint8_t v_zetaHave_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2206_; 
v_foApprox_2147_ = lean_ctor_get_uint8(v___x_2141_, 0);
v_ctxApprox_2148_ = lean_ctor_get_uint8(v___x_2141_, 1);
v_quasiPatternApprox_2149_ = lean_ctor_get_uint8(v___x_2141_, 2);
v_constApprox_2150_ = lean_ctor_get_uint8(v___x_2141_, 3);
v_isDefEqStuckEx_2151_ = lean_ctor_get_uint8(v___x_2141_, 4);
v_unificationHints_2152_ = lean_ctor_get_uint8(v___x_2141_, 5);
v_proofIrrelevance_2153_ = lean_ctor_get_uint8(v___x_2141_, 6);
v_assignSyntheticOpaque_2154_ = lean_ctor_get_uint8(v___x_2141_, 7);
v_offsetCnstrs_2155_ = lean_ctor_get_uint8(v___x_2141_, 8);
v_etaStruct_2156_ = lean_ctor_get_uint8(v___x_2141_, 10);
v_univApprox_2157_ = lean_ctor_get_uint8(v___x_2141_, 11);
v_iota_2158_ = lean_ctor_get_uint8(v___x_2141_, 12);
v_beta_2159_ = lean_ctor_get_uint8(v___x_2141_, 13);
v_proj_2160_ = lean_ctor_get_uint8(v___x_2141_, 14);
v_zeta_2161_ = lean_ctor_get_uint8(v___x_2141_, 15);
v_zetaDelta_2162_ = lean_ctor_get_uint8(v___x_2141_, 16);
v_zetaUnused_2163_ = lean_ctor_get_uint8(v___x_2141_, 17);
v_zetaHave_2164_ = lean_ctor_get_uint8(v___x_2141_, 18);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2166_ = v___x_2141_;
v_isShared_2167_ = v_isSharedCheck_2206_;
goto v_resetjp_2165_;
}
else
{
lean_dec(v___x_2141_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2206_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint8_t v_trackZetaDelta_2168_; lean_object* v_zetaDeltaSet_2169_; lean_object* v_lctx_2170_; lean_object* v_localInstances_2171_; lean_object* v_defEqCtx_x3f_2172_; lean_object* v_synthPendingDepth_2173_; lean_object* v_canUnfold_x3f_2174_; uint8_t v_univApprox_2175_; uint8_t v_inTypeClassResolution_2176_; uint8_t v_cacheInferType_2177_; lean_object* v_config_2179_; 
v_trackZetaDelta_2168_ = lean_ctor_get_uint8(v_a_2134_, sizeof(void*)*7);
v_zetaDeltaSet_2169_ = lean_ctor_get(v_a_2134_, 1);
v_lctx_2170_ = lean_ctor_get(v_a_2134_, 2);
v_localInstances_2171_ = lean_ctor_get(v_a_2134_, 3);
v_defEqCtx_x3f_2172_ = lean_ctor_get(v_a_2134_, 4);
v_synthPendingDepth_2173_ = lean_ctor_get(v_a_2134_, 5);
v_canUnfold_x3f_2174_ = lean_ctor_get(v_a_2134_, 6);
v_univApprox_2175_ = lean_ctor_get_uint8(v_a_2134_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2176_ = lean_ctor_get_uint8(v_a_2134_, sizeof(void*)*7 + 2);
v_cacheInferType_2177_ = lean_ctor_get_uint8(v_a_2134_, sizeof(void*)*7 + 3);
if (v_isShared_2167_ == 0)
{
v_config_2179_ = v___x_2166_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 0, v_foApprox_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 1, v_ctxApprox_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 2, v_quasiPatternApprox_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 3, v_constApprox_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 4, v_isDefEqStuckEx_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 5, v_unificationHints_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 6, v_proofIrrelevance_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 7, v_assignSyntheticOpaque_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 8, v_offsetCnstrs_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 10, v_etaStruct_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 11, v_univApprox_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 12, v_iota_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 13, v_beta_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 14, v_proj_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 15, v_zeta_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 16, v_zetaDelta_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 17, v_zetaUnused_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, 18, v_zetaHave_2164_);
v_config_2179_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
uint64_t v___x_2180_; uint64_t v___x_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v_key_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_ctor_set_uint8(v_config_2179_, 9, v___y_2146_);
v___x_2180_ = l_Lean_Meta_Context_configKey(v_a_2134_);
v___x_2181_ = 2ULL;
v___x_2182_ = lean_uint64_shift_right(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_uint64_shift_left(v___x_2182_, v___x_2181_);
v___x_2184_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2146_);
v_key_2185_ = lean_uint64_lor(v___x_2183_, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2186_, 0, v_config_2179_);
lean_ctor_set_uint64(v___x_2186_, sizeof(void*)*1, v_key_2185_);
lean_inc(v_canUnfold_x3f_2174_);
lean_inc(v_synthPendingDepth_2173_);
lean_inc(v_defEqCtx_x3f_2172_);
lean_inc_ref(v_localInstances_2171_);
lean_inc_ref(v_lctx_2170_);
lean_inc(v_zetaDeltaSet_2169_);
v___x_2187_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v_zetaDeltaSet_2169_);
lean_ctor_set(v___x_2187_, 2, v_lctx_2170_);
lean_ctor_set(v___x_2187_, 3, v_localInstances_2171_);
lean_ctor_set(v___x_2187_, 4, v_defEqCtx_x3f_2172_);
lean_ctor_set(v___x_2187_, 5, v_synthPendingDepth_2173_);
lean_ctor_set(v___x_2187_, 6, v_canUnfold_x3f_2174_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*7, v_trackZetaDelta_2168_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*7 + 1, v_univApprox_2175_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2176_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*7 + 3, v_cacheInferType_2177_);
lean_inc(v_a_2137_);
lean_inc_ref(v_a_2136_);
lean_inc(v_a_2135_);
lean_inc_ref(v___x_2144_);
v___x_2188_ = lean_whnf(v___x_2144_, v___x_2187_, v_a_2135_, v_a_2136_, v_a_2137_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2204_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2204_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2204_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3));
v___x_2194_ = l_Lean_Expr_isAppOf(v_a_2189_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_del_object(v___x_2191_);
lean_dec(v_a_2140_);
lean_inc_ref(v_expectedType_2133_);
v___x_2195_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed), 9, 4);
lean_closure_set(v___x_2195_, 0, v_tacticName_2132_);
lean_closure_set(v___x_2195_, 1, v_expectedType_2133_);
lean_closure_set(v___x_2195_, 2, v___x_2144_);
lean_closure_set(v___x_2195_, 3, v_a_2189_);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_mk_empty_array_with_capacity(v___x_2196_);
v___x_2198_ = lean_array_push(v___x_2197_, v_expectedType_2133_);
v___x_2199_ = l_Lean_MessageData_ofLazyM(v___x_2195_, v___x_2198_);
v___x_2200_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2199_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v___x_2200_;
}
else
{
lean_object* v___x_2202_; 
lean_dec(v_a_2189_);
lean_dec_ref(v___x_2144_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_expectedType_2133_);
lean_dec(v_tacticName_2132_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v_a_2140_);
v___x_2202_ = v___x_2191_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2140_);
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
lean_dec_ref(v___x_2144_);
lean_dec(v_a_2140_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_expectedType_2133_);
lean_dec(v_tacticName_2132_);
return v___x_2188_;
}
}
}
}
}
else
{
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_expectedType_2133_);
lean_dec(v_tacticName_2132_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(lean_object* v_tacticName_2209_, lean_object* v_expectedType_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2209_, v_expectedType_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* v_tacticName_2217_, lean_object* v_expectedType_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2217_, v_expectedType_2218_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* v_tacticName_2229_, lean_object* v_expectedType_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(v_tacticName_2229_, v_expectedType_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2240_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2));
v___x_2246_ = l_Lean_stringToMessageData(v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object* v___x_2247_, lean_object* v_tacticName_2248_, lean_object* v_expectedType_2249_, uint8_t v___x_2250_, lean_object* v_a_2251_, uint8_t v___x_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
uint8_t v___y_2259_; lean_object* v___x_2337_; uint8_t v_transparency_2338_; uint8_t v___x_2339_; 
v___x_2337_ = l_Lean_Meta_Context_config(v___y_2253_);
v_transparency_2338_ = lean_ctor_get_uint8(v___x_2337_, 9);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2338_, v___x_2252_);
if (v___x_2339_ == 0)
{
v___y_2259_ = v_transparency_2338_;
goto v___jp_2258_;
}
else
{
v___y_2259_ = v___x_2252_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2260_; uint8_t v_foApprox_2261_; uint8_t v_ctxApprox_2262_; uint8_t v_quasiPatternApprox_2263_; uint8_t v_constApprox_2264_; uint8_t v_isDefEqStuckEx_2265_; uint8_t v_unificationHints_2266_; uint8_t v_proofIrrelevance_2267_; uint8_t v_assignSyntheticOpaque_2268_; uint8_t v_offsetCnstrs_2269_; uint8_t v_etaStruct_2270_; uint8_t v_univApprox_2271_; uint8_t v_iota_2272_; uint8_t v_beta_2273_; uint8_t v_proj_2274_; uint8_t v_zeta_2275_; uint8_t v_zetaDelta_2276_; uint8_t v_zetaUnused_2277_; uint8_t v_zetaHave_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2336_; 
v___x_2260_ = l_Lean_Meta_Context_config(v___y_2253_);
v_foApprox_2261_ = lean_ctor_get_uint8(v___x_2260_, 0);
v_ctxApprox_2262_ = lean_ctor_get_uint8(v___x_2260_, 1);
v_quasiPatternApprox_2263_ = lean_ctor_get_uint8(v___x_2260_, 2);
v_constApprox_2264_ = lean_ctor_get_uint8(v___x_2260_, 3);
v_isDefEqStuckEx_2265_ = lean_ctor_get_uint8(v___x_2260_, 4);
v_unificationHints_2266_ = lean_ctor_get_uint8(v___x_2260_, 5);
v_proofIrrelevance_2267_ = lean_ctor_get_uint8(v___x_2260_, 6);
v_assignSyntheticOpaque_2268_ = lean_ctor_get_uint8(v___x_2260_, 7);
v_offsetCnstrs_2269_ = lean_ctor_get_uint8(v___x_2260_, 8);
v_etaStruct_2270_ = lean_ctor_get_uint8(v___x_2260_, 10);
v_univApprox_2271_ = lean_ctor_get_uint8(v___x_2260_, 11);
v_iota_2272_ = lean_ctor_get_uint8(v___x_2260_, 12);
v_beta_2273_ = lean_ctor_get_uint8(v___x_2260_, 13);
v_proj_2274_ = lean_ctor_get_uint8(v___x_2260_, 14);
v_zeta_2275_ = lean_ctor_get_uint8(v___x_2260_, 15);
v_zetaDelta_2276_ = lean_ctor_get_uint8(v___x_2260_, 16);
v_zetaUnused_2277_ = lean_ctor_get_uint8(v___x_2260_, 17);
v_zetaHave_2278_ = lean_ctor_get_uint8(v___x_2260_, 18);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2280_ = v___x_2260_;
v_isShared_2281_ = v_isSharedCheck_2336_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v___x_2260_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2336_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
uint8_t v_trackZetaDelta_2282_; lean_object* v_zetaDeltaSet_2283_; lean_object* v_lctx_2284_; lean_object* v_localInstances_2285_; lean_object* v_defEqCtx_x3f_2286_; lean_object* v_synthPendingDepth_2287_; lean_object* v_canUnfold_x3f_2288_; uint8_t v_univApprox_2289_; uint8_t v_inTypeClassResolution_2290_; uint8_t v_cacheInferType_2291_; lean_object* v_config_2293_; 
v_trackZetaDelta_2282_ = lean_ctor_get_uint8(v___y_2253_, sizeof(void*)*7);
v_zetaDeltaSet_2283_ = lean_ctor_get(v___y_2253_, 1);
v_lctx_2284_ = lean_ctor_get(v___y_2253_, 2);
v_localInstances_2285_ = lean_ctor_get(v___y_2253_, 3);
v_defEqCtx_x3f_2286_ = lean_ctor_get(v___y_2253_, 4);
v_synthPendingDepth_2287_ = lean_ctor_get(v___y_2253_, 5);
v_canUnfold_x3f_2288_ = lean_ctor_get(v___y_2253_, 6);
v_univApprox_2289_ = lean_ctor_get_uint8(v___y_2253_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2290_ = lean_ctor_get_uint8(v___y_2253_, sizeof(void*)*7 + 2);
v_cacheInferType_2291_ = lean_ctor_get_uint8(v___y_2253_, sizeof(void*)*7 + 3);
if (v_isShared_2281_ == 0)
{
v_config_2293_ = v___x_2280_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 0, v_foApprox_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 1, v_ctxApprox_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 2, v_quasiPatternApprox_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 3, v_constApprox_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 4, v_isDefEqStuckEx_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 5, v_unificationHints_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 6, v_proofIrrelevance_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 7, v_assignSyntheticOpaque_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 8, v_offsetCnstrs_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 10, v_etaStruct_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 11, v_univApprox_2271_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 12, v_iota_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 13, v_beta_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 14, v_proj_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 15, v_zeta_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 16, v_zetaDelta_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 17, v_zetaUnused_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, 18, v_zetaHave_2278_);
v_config_2293_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
uint64_t v___x_2294_; uint64_t v___x_2295_; uint64_t v___x_2296_; uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v_key_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_ctor_set_uint8(v_config_2293_, 9, v___y_2259_);
v___x_2294_ = l_Lean_Meta_Context_configKey(v___y_2253_);
v___x_2295_ = 2ULL;
v___x_2296_ = lean_uint64_shift_right(v___x_2294_, v___x_2295_);
v___x_2297_ = lean_uint64_shift_left(v___x_2296_, v___x_2295_);
v___x_2298_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2259_);
v_key_2299_ = lean_uint64_lor(v___x_2297_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2300_, 0, v_config_2293_);
lean_ctor_set_uint64(v___x_2300_, sizeof(void*)*1, v_key_2299_);
lean_inc(v_canUnfold_x3f_2288_);
lean_inc(v_synthPendingDepth_2287_);
lean_inc(v_defEqCtx_x3f_2286_);
lean_inc_ref(v_localInstances_2285_);
lean_inc_ref(v_lctx_2284_);
lean_inc(v_zetaDeltaSet_2283_);
v___x_2301_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v_zetaDeltaSet_2283_);
lean_ctor_set(v___x_2301_, 2, v_lctx_2284_);
lean_ctor_set(v___x_2301_, 3, v_localInstances_2285_);
lean_ctor_set(v___x_2301_, 4, v_defEqCtx_x3f_2286_);
lean_ctor_set(v___x_2301_, 5, v_synthPendingDepth_2287_);
lean_ctor_set(v___x_2301_, 6, v_canUnfold_x3f_2288_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*7, v_trackZetaDelta_2282_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*7 + 1, v_univApprox_2289_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2290_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*7 + 3, v_cacheInferType_2291_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___x_2247_);
v___x_2302_ = lean_whnf(v___x_2247_, v___x_2301_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2326_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2326_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2326_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3));
v___x_2308_ = l_Lean_Expr_isAppOf(v_a_2303_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
lean_del_object(v___x_2305_);
lean_dec_ref(v_a_2251_);
v___x_2309_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_2248_, v_expectedType_2249_, v___x_2247_, v_a_2303_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v_a_2303_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
lean_dec(v_a_2303_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_expectedType_2249_);
lean_dec_ref(v___x_2247_);
v___x_2310_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2311_ = l_Lean_MessageData_ofName(v_tacticName_2248_);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0));
v___x_2316_ = l_Lean_MessageData_ofConstName(v___x_2315_, v___x_2250_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_Exception_toMessageData(v_a_2251_);
v___x_2321_ = l_Lean_indentD(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2322_);
v___x_2324_ = v___x_2305_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_expectedType_2249_);
lean_dec(v_tacticName_2248_);
lean_dec_ref(v___x_2247_);
v_a_2327_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2302_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2302_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object* v___x_2340_, lean_object* v_tacticName_2341_, lean_object* v_expectedType_2342_, lean_object* v___x_2343_, lean_object* v_a_2344_, lean_object* v___x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v___x_5735__boxed_2351_; uint8_t v___x_5737__boxed_2352_; lean_object* v_res_2353_; 
v___x_5735__boxed_2351_ = lean_unbox(v___x_2343_);
v___x_5737__boxed_2352_ = lean_unbox(v___x_2345_);
v_res_2353_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(v___x_2340_, v_tacticName_2341_, v_expectedType_2342_, v___x_5735__boxed_2351_, v_a_2344_, v___x_5737__boxed_2352_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
return v_res_2353_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(lean_object* v_a_2354_, lean_object* v_as_2355_, size_t v_i_2356_, size_t v_stop_2357_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_usize_dec_eq(v_i_2356_, v_stop_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = lean_array_uget_borrowed(v_as_2355_, v_i_2356_);
v___x_2360_ = lean_name_eq(v_a_2354_, v___x_2359_);
if (v___x_2360_ == 0)
{
size_t v___x_2361_; size_t v___x_2362_; 
v___x_2361_ = ((size_t)1ULL);
v___x_2362_ = lean_usize_add(v_i_2356_, v___x_2361_);
v_i_2356_ = v___x_2362_;
goto _start;
}
else
{
return v___x_2360_;
}
}
else
{
uint8_t v___x_2364_; 
v___x_2364_ = 0;
return v___x_2364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(lean_object* v_a_2365_, lean_object* v_as_2366_, lean_object* v_i_2367_, lean_object* v_stop_2368_){
_start:
{
size_t v_i_boxed_2369_; size_t v_stop_boxed_2370_; uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_i_boxed_2369_ = lean_unbox_usize(v_i_2367_);
lean_dec(v_i_2367_);
v_stop_boxed_2370_ = lean_unbox_usize(v_stop_2368_);
lean_dec(v_stop_2368_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2365_, v_as_2366_, v_i_boxed_2369_, v_stop_boxed_2370_);
lean_dec_ref(v_as_2366_);
lean_dec(v_a_2365_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object* v_as_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = lean_array_get_size(v_as_2373_);
v___x_2377_ = lean_nat_dec_lt(v___x_2375_, v___x_2376_);
if (v___x_2377_ == 0)
{
return v___x_2377_;
}
else
{
if (v___x_2377_ == 0)
{
return v___x_2377_;
}
else
{
size_t v___x_2378_; size_t v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = ((size_t)0ULL);
v___x_2379_ = lean_usize_of_nat(v___x_2376_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2374_, v_as_2373_, v___x_2378_, v___x_2379_);
return v___x_2380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object* v_as_2381_, lean_object* v_a_2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v_as_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_as_2381_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(lean_object* v___x_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
if (lean_obj_tag(v_a_2386_) == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = l_List_reverse___redArg(v_a_2387_);
return v___x_2388_;
}
else
{
lean_object* v_head_2389_; lean_object* v_tail_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2400_; 
v_head_2389_ = lean_ctor_get(v_a_2386_, 0);
v_tail_2390_ = lean_ctor_get(v_a_2386_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_a_2386_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2392_ = v_a_2386_;
v_isShared_2393_ = v_isSharedCheck_2400_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_tail_2390_);
lean_inc(v_head_2389_);
lean_dec(v_a_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2400_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
uint8_t v___x_2394_; 
v___x_2394_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v___x_2385_, v_head_2389_);
if (v___x_2394_ == 0)
{
lean_del_object(v___x_2392_);
lean_dec(v_head_2389_);
v_a_2386_ = v_tail_2390_;
goto _start;
}
else
{
lean_object* v___x_2397_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 1, v_a_2387_);
v___x_2397_ = v___x_2392_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_head_2389_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_a_2387_);
v___x_2397_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
v_a_2386_ = v_tail_2390_;
v_a_2387_ = v___x_2397_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(lean_object* v___x_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v___x_2401_, v_a_2402_, v_a_2403_);
lean_dec_ref(v___x_2401_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
if (lean_obj_tag(v_a_2405_) == 0)
{
lean_object* v___x_2407_; 
v___x_2407_ = l_List_reverse___redArg(v_a_2406_);
return v___x_2407_;
}
else
{
lean_object* v_head_2408_; lean_object* v_tail_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2418_; 
v_head_2408_ = lean_ctor_get(v_a_2405_, 0);
v_tail_2409_ = lean_ctor_get(v_a_2405_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_a_2405_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2411_ = v_a_2405_;
v_isShared_2412_ = v_isSharedCheck_2418_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_tail_2409_);
lean_inc(v_head_2408_);
lean_dec(v_a_2405_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2418_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_Level_param___override(v_head_2408_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v_a_2406_);
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_a_2406_);
v___x_2415_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
v_a_2405_ = v_tail_2409_;
v_a_2406_ = v___x_2415_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_unsigned_to_nat(16u);
v___x_2421_ = lean_mk_array(v___x_2420_, v___x_2419_);
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0);
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2426_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1);
v___x_2427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
lean_ctor_set(v___x_2427_, 2, v___x_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object* v_tacticName_2428_, lean_object* v_expectedType_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2438_; 
lean_inc(v_a_2436_);
lean_inc_ref(v_a_2435_);
lean_inc(v_a_2434_);
lean_inc_ref(v_a_2433_);
lean_inc_ref(v_expectedType_2429_);
v___x_2438_ = l_Lean_Meta_mkDecideProof(v_expectedType_2429_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = l_Lean_Elab_Term_getLevelNames___redArg(v_a_2432_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_2430_, v_a_2432_, v_a_2434_, v_a_2436_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2557_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2557_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2557_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v_params_2450_; lean_object* v_fileName_2451_; lean_object* v_fileMap_2452_; lean_object* v_options_2453_; lean_object* v_currRecDepth_2454_; lean_object* v_ref_2455_; lean_object* v_currNamespace_2456_; lean_object* v_openDecls_2457_; lean_object* v_initHeartbeats_2458_; lean_object* v_maxHeartbeats_2459_; lean_object* v_quotContext_2460_; lean_object* v_currMacroScope_2461_; lean_object* v_cancelTk_x3f_2462_; uint8_t v_suppressElabErrors_2463_; lean_object* v_inheritedTraceOptions_2464_; lean_object* v_env_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; uint8_t v___x_2473_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; lean_object* v_fileName_2503_; lean_object* v_fileMap_2504_; lean_object* v_currRecDepth_2505_; lean_object* v_ref_2506_; lean_object* v_currNamespace_2507_; lean_object* v_openDecls_2508_; lean_object* v_initHeartbeats_2509_; lean_object* v_maxHeartbeats_2510_; lean_object* v_quotContext_2511_; lean_object* v_currMacroScope_2512_; lean_object* v_cancelTk_x3f_2513_; uint8_t v_suppressElabErrors_2514_; lean_object* v_inheritedTraceOptions_2515_; lean_object* v___y_2516_; uint8_t v___y_2535_; uint8_t v___x_2556_; 
v___x_2447_ = lean_st_ref_get(v_a_2436_);
v___x_2448_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2);
lean_inc_ref(v_expectedType_2429_);
v___x_2449_ = l_Lean_collectLevelParams(v___x_2448_, v_expectedType_2429_);
v_params_2450_ = lean_ctor_get(v___x_2449_, 2);
lean_inc_ref(v_params_2450_);
lean_dec_ref(v___x_2449_);
v_fileName_2451_ = lean_ctor_get(v_a_2435_, 0);
v_fileMap_2452_ = lean_ctor_get(v_a_2435_, 1);
v_options_2453_ = lean_ctor_get(v_a_2435_, 2);
v_currRecDepth_2454_ = lean_ctor_get(v_a_2435_, 3);
v_ref_2455_ = lean_ctor_get(v_a_2435_, 5);
v_currNamespace_2456_ = lean_ctor_get(v_a_2435_, 6);
v_openDecls_2457_ = lean_ctor_get(v_a_2435_, 7);
v_initHeartbeats_2458_ = lean_ctor_get(v_a_2435_, 8);
v_maxHeartbeats_2459_ = lean_ctor_get(v_a_2435_, 9);
v_quotContext_2460_ = lean_ctor_get(v_a_2435_, 10);
v_currMacroScope_2461_ = lean_ctor_get(v_a_2435_, 11);
v_cancelTk_x3f_2462_ = lean_ctor_get(v_a_2435_, 12);
v_suppressElabErrors_2463_ = lean_ctor_get_uint8(v_a_2435_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2464_ = lean_ctor_get(v_a_2435_, 13);
v_env_2465_ = lean_ctor_get(v___x_2447_, 0);
lean_inc_ref(v_env_2465_);
lean_dec(v___x_2447_);
v___x_2466_ = l_Lean_Expr_appFn_x21(v_a_2439_);
v___x_2467_ = l_Lean_Expr_appArg_x21(v___x_2466_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = l_List_reverse___redArg(v_a_2441_);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v_params_2450_, v___x_2468_, v___x_2469_);
lean_dec_ref(v_params_2450_);
v___x_2471_ = lean_box(0);
v___x_2472_ = 1;
v___x_2473_ = 0;
v___x_2498_ = l_Lean_Elab_async;
lean_inc_ref(v_options_2453_);
v___x_2499_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_2453_, v___x_2498_, v___x_2473_);
v___x_2500_ = l_Lean_diagnostics;
v___x_2501_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_2499_, v___x_2500_);
v___x_2556_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2465_);
lean_dec_ref(v_env_2465_);
if (v___x_2556_ == 0)
{
if (v___x_2501_ == 0)
{
lean_inc(v_a_2436_);
lean_inc_ref(v_inheritedTraceOptions_2464_);
lean_inc(v_cancelTk_x3f_2462_);
lean_inc(v_currMacroScope_2461_);
lean_inc(v_quotContext_2460_);
lean_inc(v_maxHeartbeats_2459_);
lean_inc(v_initHeartbeats_2458_);
lean_inc(v_openDecls_2457_);
lean_inc(v_currNamespace_2456_);
lean_inc(v_ref_2455_);
lean_inc(v_currRecDepth_2454_);
lean_inc_ref(v_fileMap_2452_);
lean_inc_ref(v_fileName_2451_);
v_fileName_2503_ = v_fileName_2451_;
v_fileMap_2504_ = v_fileMap_2452_;
v_currRecDepth_2505_ = v_currRecDepth_2454_;
v_ref_2506_ = v_ref_2455_;
v_currNamespace_2507_ = v_currNamespace_2456_;
v_openDecls_2508_ = v_openDecls_2457_;
v_initHeartbeats_2509_ = v_initHeartbeats_2458_;
v_maxHeartbeats_2510_ = v_maxHeartbeats_2459_;
v_quotContext_2511_ = v_quotContext_2460_;
v_currMacroScope_2512_ = v_currMacroScope_2461_;
v_cancelTk_x3f_2513_ = v_cancelTk_x3f_2462_;
v_suppressElabErrors_2514_ = v_suppressElabErrors_2463_;
v_inheritedTraceOptions_2515_ = v_inheritedTraceOptions_2464_;
v___y_2516_ = v_a_2436_;
goto v___jp_2502_;
}
else
{
v___y_2535_ = v___x_2556_;
goto v___jp_2534_;
}
}
else
{
v___y_2535_ = v___x_2501_;
goto v___jp_2534_;
}
v___jp_2474_:
{
if (v___y_2476_ == 0)
{
lean_object* v___x_2477_; 
lean_del_object(v___x_2445_);
v___x_2477_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2443_, v___y_2476_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2477_) == 0)
{
uint8_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v___x_2477_);
v___x_2478_ = 1;
v___x_2479_ = lean_box(v___x_2473_);
v___x_2480_ = lean_box(v___x_2478_);
lean_inc_ref(v_expectedType_2429_);
v___f_2481_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2481_, 0, v___x_2467_);
lean_closure_set(v___f_2481_, 1, v_tacticName_2428_);
lean_closure_set(v___f_2481_, 2, v_expectedType_2429_);
lean_closure_set(v___f_2481_, 3, v___x_2479_);
lean_closure_set(v___f_2481_, 4, v___y_2475_);
lean_closure_set(v___f_2481_, 5, v___x_2480_);
v___x_2482_ = lean_unsigned_to_nat(1u);
v___x_2483_ = lean_mk_empty_array_with_capacity(v___x_2482_);
v___x_2484_ = lean_array_push(v___x_2483_, v_expectedType_2429_);
v___x_2485_ = l_Lean_MessageData_ofLazyM(v___f_2481_, v___x_2484_);
v___x_2486_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2485_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
return v___x_2486_;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v___y_2475_);
lean_dec_ref(v___x_2467_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_expectedType_2429_);
lean_dec(v_tacticName_2428_);
v_a_2487_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2477_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2477_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v___x_2496_; 
lean_dec_ref(v___x_2467_);
lean_dec(v_a_2443_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_expectedType_2429_);
lean_dec(v_tacticName_2428_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 1);
lean_ctor_set(v___x_2445_, 0, v___y_2475_);
v___x_2496_ = v___x_2445_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___y_2475_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
v___jp_2502_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = l_Lean_maxRecDepth;
v___x_2518_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_2499_, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2519_, 0, v_fileName_2503_);
lean_ctor_set(v___x_2519_, 1, v_fileMap_2504_);
lean_ctor_set(v___x_2519_, 2, v___x_2499_);
lean_ctor_set(v___x_2519_, 3, v_currRecDepth_2505_);
lean_ctor_set(v___x_2519_, 4, v___x_2518_);
lean_ctor_set(v___x_2519_, 5, v_ref_2506_);
lean_ctor_set(v___x_2519_, 6, v_currNamespace_2507_);
lean_ctor_set(v___x_2519_, 7, v_openDecls_2508_);
lean_ctor_set(v___x_2519_, 8, v_initHeartbeats_2509_);
lean_ctor_set(v___x_2519_, 9, v_maxHeartbeats_2510_);
lean_ctor_set(v___x_2519_, 10, v_quotContext_2511_);
lean_ctor_set(v___x_2519_, 11, v_currMacroScope_2512_);
lean_ctor_set(v___x_2519_, 12, v_cancelTk_x3f_2513_);
lean_ctor_set(v___x_2519_, 13, v_inheritedTraceOptions_2515_);
lean_ctor_set_uint8(v___x_2519_, sizeof(void*)*14, v___x_2501_);
lean_ctor_set_uint8(v___x_2519_, sizeof(void*)*14 + 1, v_suppressElabErrors_2514_);
lean_inc(v_a_2434_);
lean_inc_ref(v_a_2433_);
lean_inc_ref(v_expectedType_2429_);
lean_inc(v___x_2470_);
v___x_2520_ = l_Lean_Meta_mkAuxLemma(v___x_2470_, v_expectedType_2429_, v_a_2439_, v___x_2471_, v___x_2472_, v___x_2473_, v___x_2473_, v_a_2433_, v_a_2434_, v___x_2519_, v___y_2516_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v___x_2467_);
lean_del_object(v___x_2445_);
lean_dec(v_a_2443_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_expectedType_2429_);
lean_dec(v_tacticName_2428_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2530_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2530_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2525_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(v___x_2470_, v___x_2469_);
v___x_2526_ = l_Lean_mkConst(v_a_2521_, v___x_2525_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2526_);
v___x_2528_ = v___x_2523_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2531_; uint8_t v___x_2532_; 
lean_dec(v___x_2470_);
v_a_2531_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2531_);
lean_dec_ref(v___x_2520_);
v___x_2532_ = l_Lean_Exception_isInterrupt(v_a_2531_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
lean_inc(v_a_2531_);
v___x_2533_ = l_Lean_Exception_isRuntime(v_a_2531_);
v___y_2475_ = v_a_2531_;
v___y_2476_ = v___x_2533_;
goto v___jp_2474_;
}
else
{
v___y_2475_ = v_a_2531_;
v___y_2476_ = v___x_2532_;
goto v___jp_2474_;
}
}
}
v___jp_2534_:
{
if (v___y_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v_env_2537_; lean_object* v_nextMacroScope_2538_; lean_object* v_ngen_2539_; lean_object* v_auxDeclNGen_2540_; lean_object* v_traceState_2541_; lean_object* v_messages_2542_; lean_object* v_infoState_2543_; lean_object* v_snapshotTasks_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2554_; 
v___x_2536_ = lean_st_ref_take(v_a_2436_);
v_env_2537_ = lean_ctor_get(v___x_2536_, 0);
v_nextMacroScope_2538_ = lean_ctor_get(v___x_2536_, 1);
v_ngen_2539_ = lean_ctor_get(v___x_2536_, 2);
v_auxDeclNGen_2540_ = lean_ctor_get(v___x_2536_, 3);
v_traceState_2541_ = lean_ctor_get(v___x_2536_, 4);
v_messages_2542_ = lean_ctor_get(v___x_2536_, 6);
v_infoState_2543_ = lean_ctor_get(v___x_2536_, 7);
v_snapshotTasks_2544_ = lean_ctor_get(v___x_2536_, 8);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2536_, 5);
lean_dec(v_unused_2555_);
v___x_2546_ = v___x_2536_;
v_isShared_2547_ = v_isSharedCheck_2554_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_snapshotTasks_2544_);
lean_inc(v_infoState_2543_);
lean_inc(v_messages_2542_);
lean_inc(v_traceState_2541_);
lean_inc(v_auxDeclNGen_2540_);
lean_inc(v_ngen_2539_);
lean_inc(v_nextMacroScope_2538_);
lean_inc(v_env_2537_);
lean_dec(v___x_2536_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2554_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2548_ = l_Lean_Kernel_enableDiag(v_env_2537_, v___x_2501_);
v___x_2549_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 5, v___x_2549_);
lean_ctor_set(v___x_2546_, 0, v___x_2548_);
v___x_2551_ = v___x_2546_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_nextMacroScope_2538_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_ngen_2539_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_auxDeclNGen_2540_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_traceState_2541_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2553_, 6, v_messages_2542_);
lean_ctor_set(v_reuseFailAlloc_2553_, 7, v_infoState_2543_);
lean_ctor_set(v_reuseFailAlloc_2553_, 8, v_snapshotTasks_2544_);
v___x_2551_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_st_ref_set(v_a_2436_, v___x_2551_);
lean_inc(v_a_2436_);
lean_inc_ref(v_inheritedTraceOptions_2464_);
lean_inc(v_cancelTk_x3f_2462_);
lean_inc(v_currMacroScope_2461_);
lean_inc(v_quotContext_2460_);
lean_inc(v_maxHeartbeats_2459_);
lean_inc(v_initHeartbeats_2458_);
lean_inc(v_openDecls_2457_);
lean_inc(v_currNamespace_2456_);
lean_inc(v_ref_2455_);
lean_inc(v_currRecDepth_2454_);
lean_inc_ref(v_fileMap_2452_);
lean_inc_ref(v_fileName_2451_);
v_fileName_2503_ = v_fileName_2451_;
v_fileMap_2504_ = v_fileMap_2452_;
v_currRecDepth_2505_ = v_currRecDepth_2454_;
v_ref_2506_ = v_ref_2455_;
v_currNamespace_2507_ = v_currNamespace_2456_;
v_openDecls_2508_ = v_openDecls_2457_;
v_initHeartbeats_2509_ = v_initHeartbeats_2458_;
v_maxHeartbeats_2510_ = v_maxHeartbeats_2459_;
v_quotContext_2511_ = v_quotContext_2460_;
v_currMacroScope_2512_ = v_currMacroScope_2461_;
v_cancelTk_x3f_2513_ = v_cancelTk_x3f_2462_;
v_suppressElabErrors_2514_ = v_suppressElabErrors_2463_;
v_inheritedTraceOptions_2515_ = v_inheritedTraceOptions_2464_;
v___y_2516_ = v_a_2436_;
goto v___jp_2502_;
}
}
}
else
{
lean_inc(v_a_2436_);
lean_inc_ref(v_inheritedTraceOptions_2464_);
lean_inc(v_cancelTk_x3f_2462_);
lean_inc(v_currMacroScope_2461_);
lean_inc(v_quotContext_2460_);
lean_inc(v_maxHeartbeats_2459_);
lean_inc(v_initHeartbeats_2458_);
lean_inc(v_openDecls_2457_);
lean_inc(v_currNamespace_2456_);
lean_inc(v_ref_2455_);
lean_inc(v_currRecDepth_2454_);
lean_inc_ref(v_fileMap_2452_);
lean_inc_ref(v_fileName_2451_);
v_fileName_2503_ = v_fileName_2451_;
v_fileMap_2504_ = v_fileMap_2452_;
v_currRecDepth_2505_ = v_currRecDepth_2454_;
v_ref_2506_ = v_ref_2455_;
v_currNamespace_2507_ = v_currNamespace_2456_;
v_openDecls_2508_ = v_openDecls_2457_;
v_initHeartbeats_2509_ = v_initHeartbeats_2458_;
v_maxHeartbeats_2510_ = v_maxHeartbeats_2459_;
v_quotContext_2511_ = v_quotContext_2460_;
v_currMacroScope_2512_ = v_currMacroScope_2461_;
v_cancelTk_x3f_2513_ = v_cancelTk_x3f_2462_;
v_suppressElabErrors_2514_ = v_suppressElabErrors_2463_;
v_inheritedTraceOptions_2515_ = v_inheritedTraceOptions_2464_;
v___y_2516_ = v_a_2436_;
goto v___jp_2502_;
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_a_2441_);
lean_dec(v_a_2439_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_expectedType_2429_);
lean_dec(v_tacticName_2428_);
v_a_2558_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2442_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2442_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2439_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_expectedType_2429_);
lean_dec(v_tacticName_2428_);
v_a_2566_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2440_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2440_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_expectedType_2429_);
lean_dec(v_tacticName_2428_);
return v___x_2438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object* v_tacticName_2574_, lean_object* v_expectedType_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2574_, v_expectedType_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* v_tacticName_2585_, lean_object* v_expectedType_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2585_, v_expectedType_2586_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* v_tacticName_2597_, lean_object* v_expectedType_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(v_tacticName_2597_, v_expectedType_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
return v_res_2608_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t v_native_2612_, uint8_t v_kernel_2613_, lean_object* v_tacticName_2614_, lean_object* v_expectedType_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; 
if (v_kernel_2613_ == 0)
{
v___y_2627_ = v___y_2617_;
v___y_2628_ = v___y_2618_;
v___y_2629_ = v___y_2619_;
v___y_2630_ = v___y_2620_;
v___y_2631_ = v___y_2621_;
v___y_2632_ = v___y_2622_;
v___y_2633_ = v___y_2623_;
v___y_2634_ = v___y_2624_;
goto v___jp_2626_;
}
else
{
if (v_native_2612_ == 0)
{
v___y_2627_ = v___y_2617_;
v___y_2628_ = v___y_2618_;
v___y_2629_ = v___y_2619_;
v___y_2630_ = v___y_2620_;
v___y_2631_ = v___y_2621_;
v___y_2632_ = v___y_2622_;
v___y_2633_ = v___y_2623_;
v___y_2634_ = v___y_2624_;
goto v___jp_2626_;
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref(v___y_2619_);
lean_dec_ref(v_expectedType_2615_);
v___x_2642_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2643_ = l_Lean_MessageData_ofName(v_tacticName_2614_);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_obj_once(&l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1, &l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1);
v___x_2646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2646_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
v___jp_2626_:
{
lean_object* v___x_2635_; 
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc_ref(v___y_2629_);
v___x_2635_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_2615_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
if (v_native_2612_ == 0)
{
if (v_kernel_2613_ == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; 
lean_dec_ref(v___y_2629_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v___x_2635_);
v___x_2637_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2614_, v_a_2636_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2637_;
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2635_);
v___x_2639_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2614_, v_a_2638_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec_ref(v___y_2629_);
return v___x_2639_;
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2635_);
v___x_2641_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_2614_, v_a_2640_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec_ref(v___y_2629_);
return v___x_2641_;
}
}
else
{
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v___y_2629_);
lean_dec(v_tacticName_2614_);
return v___x_2635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object* v_native_2656_, lean_object* v_kernel_2657_, lean_object* v_tacticName_2658_, lean_object* v_expectedType_2659_, lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v_native_boxed_2670_; uint8_t v_kernel_boxed_2671_; lean_object* v_res_2672_; 
v_native_boxed_2670_ = lean_unbox(v_native_2656_);
v_kernel_boxed_2671_ = lean_unbox(v_kernel_2657_);
v_res_2672_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0(v_native_boxed_2670_, v_kernel_boxed_2671_, v_tacticName_2658_, v_expectedType_2659_, v_x_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2664_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v_x_2660_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t v_revert_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2675_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref(v___x_2683_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
v___x_2686_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_a_2684_, v___x_2685_, v_revert_2673_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2686_);
lean_inc(v_a_2687_);
v___x_2688_ = l_Lean_MVarId_getDecl(v_a_2687_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v_lctx_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
v_lctx_2690_ = lean_ctor_get(v_a_2689_, 1);
lean_inc_ref(v_lctx_2690_);
lean_dec(v_a_2689_);
v___x_2691_ = l_Lean_LocalContext_getFVarIds(v_lctx_2690_);
lean_dec_ref(v_lctx_2690_);
v___x_2692_ = 0;
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2680_);
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
v___x_2693_ = l_Lean_MVarId_revert(v_a_2687_, v___x_2691_, v___x_2692_, v_revert_2673_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2704_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
v_snd_2695_ = lean_ctor_get(v_a_2694_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_a_2694_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_a_2694_, 0);
lean_dec(v_unused_2705_);
v___x_2697_ = v_a_2694_;
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_dec(v_a_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = lean_box(0);
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 1, v___x_2699_);
lean_ctor_set(v___x_2697_, 0, v_snd_2695_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_snd_2695_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2701_, v___y_2675_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v___x_2702_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
v_a_2706_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2693_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2693_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2687_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
v_a_2714_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2688_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2688_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
v_a_2722_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2686_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2686_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
v_a_2730_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2683_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2683_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object* v_revert_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v_revert_boxed_2748_; lean_object* v_res_2749_; 
v_revert_boxed_2748_ = lean_unbox(v_revert_2738_);
v_res_2749_ = l_Lean_Elab_Tactic_evalDecideCore___lam__1(v_revert_boxed_2748_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* v_tacticName_2750_, lean_object* v_cfg_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
uint8_t v_kernel_2761_; uint8_t v_native_2762_; uint8_t v_revert_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; 
v_kernel_2761_ = lean_ctor_get_uint8(v_cfg_2751_, 0);
v_native_2762_ = lean_ctor_get_uint8(v_cfg_2751_, 1);
v_revert_2763_ = lean_ctor_get_uint8(v_cfg_2751_, 3);
v___x_2764_ = lean_box(v_native_2762_);
v___x_2765_ = lean_box(v_kernel_2761_);
lean_inc(v_tacticName_2750_);
v___f_2766_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2766_, 0, v___x_2764_);
lean_closure_set(v___f_2766_, 1, v___x_2765_);
lean_closure_set(v___f_2766_, 2, v_tacticName_2750_);
if (v_revert_2763_ == 0)
{
v___y_2768_ = v_a_2752_;
v___y_2769_ = v_a_2753_;
v___y_2770_ = v_a_2754_;
v___y_2771_ = v_a_2755_;
v___y_2772_ = v_a_2756_;
v___y_2773_ = v_a_2757_;
v___y_2774_ = v_a_2758_;
v___y_2775_ = v_a_2759_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_box(v_revert_2763_);
v___f_2779_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2779_, 0, v___x_2778_);
lean_inc(v_a_2759_);
lean_inc_ref(v_a_2758_);
lean_inc(v_a_2757_);
lean_inc_ref(v_a_2756_);
lean_inc(v_a_2755_);
lean_inc_ref(v_a_2754_);
lean_inc(v_a_2753_);
lean_inc_ref(v_a_2752_);
v___x_2780_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2779_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_dec_ref(v___x_2780_);
v___y_2768_ = v_a_2752_;
v___y_2769_ = v_a_2753_;
v___y_2770_ = v_a_2754_;
v___y_2771_ = v_a_2755_;
v___y_2772_ = v_a_2756_;
v___y_2773_ = v_a_2757_;
v___y_2774_ = v_a_2758_;
v___y_2775_ = v_a_2759_;
goto v___jp_2767_;
}
else
{
lean_dec_ref(v___f_2766_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_tacticName_2750_);
return v___x_2780_;
}
}
v___jp_2767_:
{
uint8_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = 1;
v___x_2777_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacticName_2750_, v___f_2766_, v___x_2776_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
return v___x_2777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object* v_tacticName_2781_, lean_object* v_cfg_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_Elab_Tactic_evalDecideCore(v_tacticName_2781_, v_cfg_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec_ref(v_cfg_2782_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(lean_object* v_e_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; uint8_t v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_2809_ = 0;
v___x_2810_ = 1;
v___x_2811_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_2808_, v_e_2802_, v___x_2809_, v___x_2810_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3____boxed(lean_object* v_e_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v_e_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(lean_object* v_e_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v_e_2819_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3____boxed(lean_object* v_e_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v_e_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg(lean_object* v_a_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_box(0);
return v___x_2839_;
}
else
{
lean_object* v_key_2840_; lean_object* v_value_2841_; lean_object* v_tail_2842_; uint8_t v___x_2843_; 
v_key_2840_ = lean_ctor_get(v_x_2838_, 0);
v_value_2841_ = lean_ctor_get(v_x_2838_, 1);
v_tail_2842_ = lean_ctor_get(v_x_2838_, 2);
v___x_2843_ = lean_name_eq(v_key_2840_, v_a_2837_);
if (v___x_2843_ == 0)
{
v_x_2838_ = v_tail_2842_;
goto _start;
}
else
{
lean_object* v___x_2845_; 
lean_inc(v_value_2841_);
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_value_2841_);
return v___x_2845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_2846_, lean_object* v_x_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg(v_a_2846_, v_x_2847_);
lean_dec(v_x_2847_);
lean_dec(v_a_2846_);
return v_res_2848_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2849_; uint64_t v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(1723u);
v___x_2850_ = lean_uint64_of_nat(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(lean_object* v_m_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_buckets_2853_; lean_object* v___x_2854_; uint64_t v___y_2856_; 
v_buckets_2853_ = lean_ctor_get(v_m_2851_, 1);
v___x_2854_ = lean_array_get_size(v_buckets_2853_);
if (lean_obj_tag(v_a_2852_) == 0)
{
uint64_t v___x_2870_; 
v___x_2870_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0);
v___y_2856_ = v___x_2870_;
goto v___jp_2855_;
}
else
{
uint64_t v_hash_2871_; 
v_hash_2871_ = lean_ctor_get_uint64(v_a_2852_, sizeof(void*)*2);
v___y_2856_ = v_hash_2871_;
goto v___jp_2855_;
}
v___jp_2855_:
{
uint64_t v___x_2857_; uint64_t v___x_2858_; uint64_t v_fold_2859_; uint64_t v___x_2860_; uint64_t v___x_2861_; uint64_t v___x_2862_; size_t v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; size_t v___x_2866_; size_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2857_ = 32ULL;
v___x_2858_ = lean_uint64_shift_right(v___y_2856_, v___x_2857_);
v_fold_2859_ = lean_uint64_xor(v___y_2856_, v___x_2858_);
v___x_2860_ = 16ULL;
v___x_2861_ = lean_uint64_shift_right(v_fold_2859_, v___x_2860_);
v___x_2862_ = lean_uint64_xor(v_fold_2859_, v___x_2861_);
v___x_2863_ = lean_uint64_to_usize(v___x_2862_);
v___x_2864_ = lean_usize_of_nat(v___x_2854_);
v___x_2865_ = ((size_t)1ULL);
v___x_2866_ = lean_usize_sub(v___x_2864_, v___x_2865_);
v___x_2867_ = lean_usize_land(v___x_2863_, v___x_2866_);
v___x_2868_ = lean_array_uget_borrowed(v_buckets_2853_, v___x_2867_);
v___x_2869_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg(v_a_2852_, v___x_2868_);
return v___x_2869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(v_m_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_m_2872_);
return v_res_2874_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_2875_, lean_object* v_i_2876_, lean_object* v_k_2877_){
_start:
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = lean_array_get_size(v_keys_2875_);
v___x_2879_ = lean_nat_dec_lt(v_i_2876_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_dec(v_i_2876_);
return v___x_2879_;
}
else
{
lean_object* v_k_x27_2880_; uint8_t v___x_2881_; 
v_k_x27_2880_ = lean_array_fget_borrowed(v_keys_2875_, v_i_2876_);
v___x_2881_ = l_Lean_instBEqExtraModUse_beq(v_k_2877_, v_k_x27_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_nat_add(v_i_2876_, v___x_2882_);
lean_dec(v_i_2876_);
v_i_2876_ = v___x_2883_;
goto _start;
}
else
{
lean_dec(v_i_2876_);
return v___x_2881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_2885_, lean_object* v_i_2886_, lean_object* v_k_2887_){
_start:
{
uint8_t v_res_2888_; lean_object* v_r_2889_; 
v_res_2888_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg(v_keys_2885_, v_i_2886_, v_k_2887_);
lean_dec_ref(v_k_2887_);
lean_dec_ref(v_keys_2885_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; 
v___x_2890_ = ((size_t)5ULL);
v___x_2891_ = ((size_t)1ULL);
v___x_2892_ = lean_usize_shift_left(v___x_2891_, v___x_2890_);
return v___x_2892_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; 
v___x_2893_ = ((size_t)1ULL);
v___x_2894_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_2895_ = lean_usize_sub(v___x_2894_, v___x_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2896_, size_t v_x_2897_, lean_object* v_x_2898_){
_start:
{
if (lean_obj_tag(v_x_2896_) == 0)
{
lean_object* v_es_2899_; lean_object* v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; lean_object* v_j_2904_; lean_object* v___x_2905_; 
v_es_2899_ = lean_ctor_get(v_x_2896_, 0);
lean_inc_ref(v_es_2899_);
lean_dec_ref(v_x_2896_);
v___x_2900_ = lean_box(2);
v___x_2901_ = ((size_t)5ULL);
v___x_2902_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2903_ = lean_usize_land(v_x_2897_, v___x_2902_);
v_j_2904_ = lean_usize_to_nat(v___x_2903_);
v___x_2905_ = lean_array_get(v___x_2900_, v_es_2899_, v_j_2904_);
lean_dec(v_j_2904_);
lean_dec_ref(v_es_2899_);
switch(lean_obj_tag(v___x_2905_))
{
case 0:
{
lean_object* v_key_2906_; uint8_t v___x_2907_; 
v_key_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_key_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = l_Lean_instBEqExtraModUse_beq(v_x_2898_, v_key_2906_);
lean_dec(v_key_2906_);
return v___x_2907_;
}
case 1:
{
lean_object* v_node_2908_; size_t v___x_2909_; 
v_node_2908_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_node_2908_);
lean_dec_ref(v___x_2905_);
v___x_2909_ = lean_usize_shift_right(v_x_2897_, v___x_2901_);
v_x_2896_ = v_node_2908_;
v_x_2897_ = v___x_2909_;
goto _start;
}
default: 
{
uint8_t v___x_2911_; 
v___x_2911_ = 0;
return v___x_2911_;
}
}
}
else
{
lean_object* v_ks_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_ks_2912_ = lean_ctor_get(v_x_2896_, 0);
lean_inc_ref(v_ks_2912_);
lean_dec_ref(v_x_2896_);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg(v_ks_2912_, v___x_2913_, v_x_2898_);
lean_dec_ref(v_ks_2912_);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
size_t v_x_10467__boxed_2918_; uint8_t v_res_2919_; lean_object* v_r_2920_; 
v_x_10467__boxed_2918_ = lean_unbox_usize(v_x_2916_);
lean_dec(v_x_2916_);
v_res_2919_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2915_, v_x_10467__boxed_2918_, v_x_2917_);
lean_dec_ref(v_x_2917_);
v_r_2920_ = lean_box(v_res_2919_);
return v_r_2920_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2921_, lean_object* v_x_2922_){
_start:
{
uint64_t v___x_2923_; size_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2923_ = l_Lean_instHashableExtraModUse_hash(v_x_2922_);
v___x_2924_ = lean_uint64_to_usize(v___x_2923_);
v___x_2925_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2921_, v___x_2924_, v_x_2922_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2926_, lean_object* v_x_2927_){
_start:
{
uint8_t v_res_2928_; lean_object* v_r_2929_; 
v_res_2928_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_2926_, v_x_2927_);
lean_dec_ref(v_x_2927_);
v_r_2929_ = lean_box(v_res_2928_);
return v_r_2929_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2930_; double v___x_2931_; 
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_float_of_nat(v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg(lean_object* v_cls_2933_, lean_object* v_msg_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_ref_2940_; lean_object* v___x_2941_; lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2986_; 
v_ref_2940_ = lean_ctor_get(v___y_2937_, 5);
v___x_2941_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2986_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2986_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v_traceState_2947_; lean_object* v_env_2948_; lean_object* v_nextMacroScope_2949_; lean_object* v_ngen_2950_; lean_object* v_auxDeclNGen_2951_; lean_object* v_cache_2952_; lean_object* v_messages_2953_; lean_object* v_infoState_2954_; lean_object* v_snapshotTasks_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2985_; 
v___x_2946_ = lean_st_ref_take(v___y_2938_);
v_traceState_2947_ = lean_ctor_get(v___x_2946_, 4);
v_env_2948_ = lean_ctor_get(v___x_2946_, 0);
v_nextMacroScope_2949_ = lean_ctor_get(v___x_2946_, 1);
v_ngen_2950_ = lean_ctor_get(v___x_2946_, 2);
v_auxDeclNGen_2951_ = lean_ctor_get(v___x_2946_, 3);
v_cache_2952_ = lean_ctor_get(v___x_2946_, 5);
v_messages_2953_ = lean_ctor_get(v___x_2946_, 6);
v_infoState_2954_ = lean_ctor_get(v___x_2946_, 7);
v_snapshotTasks_2955_ = lean_ctor_get(v___x_2946_, 8);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2957_ = v___x_2946_;
v_isShared_2958_ = v_isSharedCheck_2985_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_snapshotTasks_2955_);
lean_inc(v_infoState_2954_);
lean_inc(v_messages_2953_);
lean_inc(v_cache_2952_);
lean_inc(v_traceState_2947_);
lean_inc(v_auxDeclNGen_2951_);
lean_inc(v_ngen_2950_);
lean_inc(v_nextMacroScope_2949_);
lean_inc(v_env_2948_);
lean_dec(v___x_2946_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2985_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
uint64_t v_tid_2959_; lean_object* v_traces_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2984_; 
v_tid_2959_ = lean_ctor_get_uint64(v_traceState_2947_, sizeof(void*)*1);
v_traces_2960_ = lean_ctor_get(v_traceState_2947_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_traceState_2947_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2962_ = v_traceState_2947_;
v_isShared_2963_ = v_isSharedCheck_2984_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_traces_2960_);
lean_dec(v_traceState_2947_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2984_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; double v___x_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_2966_ = 0;
v___x_2967_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_2968_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2968_, 0, v_cls_2933_);
lean_ctor_set(v___x_2968_, 1, v___x_2964_);
lean_ctor_set(v___x_2968_, 2, v___x_2967_);
lean_ctor_set_float(v___x_2968_, sizeof(void*)*3, v___x_2965_);
lean_ctor_set_float(v___x_2968_, sizeof(void*)*3 + 8, v___x_2965_);
lean_ctor_set_uint8(v___x_2968_, sizeof(void*)*3 + 16, v___x_2966_);
v___x_2969_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0));
v___x_2970_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v_a_2942_);
lean_ctor_set(v___x_2970_, 2, v___x_2969_);
lean_inc(v_ref_2940_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_ref_2940_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = l_Lean_PersistentArray_push___redArg(v_traces_2960_, v___x_2971_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2972_);
v___x_2974_ = v___x_2962_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2972_);
lean_ctor_set_uint64(v_reuseFailAlloc_2983_, sizeof(void*)*1, v_tid_2959_);
v___x_2974_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 4, v___x_2974_);
v___x_2976_ = v___x_2957_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_env_2948_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_nextMacroScope_2949_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_ngen_2950_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_auxDeclNGen_2951_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_cache_2952_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_messages_2953_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_infoState_2954_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_snapshotTasks_2955_);
v___x_2976_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2977_ = lean_st_ref_set(v___y_2938_, v___x_2976_);
v___x_2978_ = lean_box(0);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2978_);
v___x_2980_ = v___x_2944_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_cls_2987_, lean_object* v_msg_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg(v_cls_2987_, v_msg_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v_options_2998_; uint8_t v_hasTrace_2999_; 
v_options_2998_ = lean_ctor_get(v___y_2996_, 2);
v_hasTrace_2999_ = lean_ctor_get_uint8(v_options_2998_, sizeof(void*)*1);
if (v_hasTrace_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v_cls_2995_);
v___x_3000_ = lean_box(v_hasTrace_2999_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
else
{
lean_object* v_inheritedTraceOptions_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_inheritedTraceOptions_3002_ = lean_ctor_get(v___y_2996_, 13);
v___x_3003_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1));
v___x_3004_ = l_Lean_Name_append(v___x_3003_, v_cls_2995_);
v___x_3005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3002_, v_options_2998_, v___x_3004_);
lean_dec(v___x_3004_);
v___x_3006_ = lean_box(v___x_3005_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_3008_, v___y_3009_);
lean_dec_ref(v___y_3009_);
return v_res_3011_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__1));
v___x_3015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__0));
v___x_3016_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
v___x_3018_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
lean_ctor_set(v___x_3018_, 2, v___x_3017_);
lean_ctor_set(v___x_3018_, 3, v___x_3017_);
lean_ctor_set(v___x_3018_, 4, v___x_3017_);
lean_ctor_set(v___x_3018_, 5, v___x_3017_);
return v___x_3018_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__6));
v___x_3024_ = l_Lean_stringToMessageData(v___x_3023_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__8));
v___x_3027_ = l_Lean_stringToMessageData(v___x_3026_);
return v___x_3027_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_3029_ = l_Lean_stringToMessageData(v___x_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(lean_object* v_mod_3037_, uint8_t v_isMeta_3038_, lean_object* v_hint_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; lean_object* v_env_3048_; uint8_t v_isExporting_3049_; lean_object* v___x_3050_; lean_object* v_env_3051_; lean_object* v___x_3052_; lean_object* v_entry_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3047_ = lean_st_ref_get(v___y_3045_);
v_env_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc_ref(v_env_3048_);
lean_dec(v___x_3047_);
v_isExporting_3049_ = lean_ctor_get_uint8(v_env_3048_, sizeof(void*)*8);
lean_dec_ref(v_env_3048_);
v___x_3050_ = lean_st_ref_get(v___y_3045_);
v_env_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc_ref(v_env_3051_);
lean_dec(v___x_3050_);
v___x_3052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_3037_);
v_entry_3053_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3053_, 0, v_mod_3037_);
lean_ctor_set_uint8(v_entry_3053_, sizeof(void*)*1, v_isExporting_3049_);
lean_ctor_set_uint8(v_entry_3053_, sizeof(void*)*1 + 1, v_isMeta_3038_);
v___x_3054_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3055_ = lean_box(1);
v___x_3056_ = lean_box(0);
v___x_3099_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3052_, v___x_3054_, v_env_3051_, v___x_3055_, v___x_3056_);
v___x_3100_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(v___x_3099_, v_entry_3053_);
if (v___x_3100_ == 0)
{
lean_object* v_cls_3101_; lean_object* v___x_3102_; lean_object* v_a_3103_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3110_; lean_object* v___y_3111_; uint8_t v___x_3123_; 
v_cls_3101_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__5));
v___x_3102_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_3101_, v___y_3044_);
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref(v___x_3102_);
v___x_3123_ = lean_unbox(v_a_3103_);
lean_dec(v_a_3103_);
if (v___x_3123_ == 0)
{
lean_dec(v_hint_3039_);
lean_dec(v_mod_3037_);
v___y_3058_ = v___y_3043_;
v___y_3059_ = v___y_3045_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3124_; lean_object* v___y_3126_; 
v___x_3124_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12);
if (v_isExporting_3049_ == 0)
{
lean_object* v___x_3133_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15));
v___y_3126_ = v___x_3133_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3134_; 
v___x_3134_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16));
v___y_3126_ = v___x_3134_;
goto v___jp_3125_;
}
v___jp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3127_ = l_Lean_stringToMessageData(v___y_3126_);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3124_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
if (v_isMeta_3038_ == 0)
{
lean_object* v___x_3131_; 
v___x_3131_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13));
v___y_3110_ = v___x_3130_;
v___y_3111_ = v___x_3131_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3132_; 
v___x_3132_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14));
v___y_3110_ = v___x_3130_;
v___y_3111_ = v___x_3132_;
goto v___jp_3109_;
}
}
}
v___jp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___y_3105_);
lean_ctor_set(v___x_3107_, 1, v___y_3106_);
v___x_3108_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg(v_cls_3101_, v___x_3107_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_dec_ref(v___x_3108_);
v___y_3058_ = v___y_3043_;
v___y_3059_ = v___y_3045_;
goto v___jp_3057_;
}
else
{
lean_dec_ref(v_entry_3053_);
return v___x_3108_;
}
}
v___jp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3112_ = l_Lean_stringToMessageData(v___y_3111_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___y_3110_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = l_Lean_MessageData_ofName(v_mod_3037_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_Name_isAnonymous(v_hint_3039_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9);
v___x_3120_ = l_Lean_MessageData_ofName(v_hint_3039_);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___y_3105_ = v___x_3117_;
v___y_3106_ = v___x_3121_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3122_; 
lean_dec(v_hint_3039_);
v___x_3122_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10);
v___y_3105_ = v___x_3117_;
v___y_3106_ = v___x_3122_;
goto v___jp_3104_;
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec_ref(v_entry_3053_);
lean_dec(v_hint_3039_);
lean_dec(v_mod_3037_);
v___x_3135_ = lean_box(0);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
v___jp_3057_:
{
lean_object* v___x_3060_; lean_object* v_toEnvExtension_3061_; lean_object* v_env_3062_; lean_object* v_nextMacroScope_3063_; lean_object* v_ngen_3064_; lean_object* v_auxDeclNGen_3065_; lean_object* v_traceState_3066_; lean_object* v_messages_3067_; lean_object* v_infoState_3068_; lean_object* v_snapshotTasks_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3097_; 
v___x_3060_ = lean_st_ref_take(v___y_3059_);
v_toEnvExtension_3061_ = lean_ctor_get(v___x_3054_, 0);
lean_inc_ref(v_toEnvExtension_3061_);
v_env_3062_ = lean_ctor_get(v___x_3060_, 0);
v_nextMacroScope_3063_ = lean_ctor_get(v___x_3060_, 1);
v_ngen_3064_ = lean_ctor_get(v___x_3060_, 2);
v_auxDeclNGen_3065_ = lean_ctor_get(v___x_3060_, 3);
v_traceState_3066_ = lean_ctor_get(v___x_3060_, 4);
v_messages_3067_ = lean_ctor_get(v___x_3060_, 6);
v_infoState_3068_ = lean_ctor_get(v___x_3060_, 7);
v_snapshotTasks_3069_ = lean_ctor_get(v___x_3060_, 8);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v___x_3060_, 5);
lean_dec(v_unused_3098_);
v___x_3071_ = v___x_3060_;
v_isShared_3072_ = v_isSharedCheck_3097_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_snapshotTasks_3069_);
lean_inc(v_infoState_3068_);
lean_inc(v_messages_3067_);
lean_inc(v_traceState_3066_);
lean_inc(v_auxDeclNGen_3065_);
lean_inc(v_ngen_3064_);
lean_inc(v_nextMacroScope_3063_);
lean_inc(v_env_3062_);
lean_dec(v___x_3060_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3097_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_asyncMode_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v_asyncMode_3073_ = lean_ctor_get(v_toEnvExtension_3061_, 2);
lean_inc(v_asyncMode_3073_);
lean_dec_ref(v_toEnvExtension_3061_);
v___x_3074_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3054_, v_env_3062_, v_entry_3053_, v_asyncMode_3073_, v___x_3056_);
lean_dec(v_asyncMode_3073_);
v___x_3075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 5, v___x_3075_);
lean_ctor_set(v___x_3071_, 0, v___x_3074_);
v___x_3077_ = v___x_3071_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3074_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_nextMacroScope_3063_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_ngen_3064_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_auxDeclNGen_3065_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_traceState_3066_);
lean_ctor_set(v_reuseFailAlloc_3096_, 5, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3096_, 6, v_messages_3067_);
lean_ctor_set(v_reuseFailAlloc_3096_, 7, v_infoState_3068_);
lean_ctor_set(v_reuseFailAlloc_3096_, 8, v_snapshotTasks_3069_);
v___x_3077_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v_mctx_3080_; lean_object* v_zetaDeltaFVarIds_3081_; lean_object* v_postponed_3082_; lean_object* v_diag_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3094_; 
v___x_3078_ = lean_st_ref_set(v___y_3059_, v___x_3077_);
v___x_3079_ = lean_st_ref_take(v___y_3058_);
v_mctx_3080_ = lean_ctor_get(v___x_3079_, 0);
v_zetaDeltaFVarIds_3081_ = lean_ctor_get(v___x_3079_, 2);
v_postponed_3082_ = lean_ctor_get(v___x_3079_, 3);
v_diag_3083_ = lean_ctor_get(v___x_3079_, 4);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; 
v_unused_3095_ = lean_ctor_get(v___x_3079_, 1);
lean_dec(v_unused_3095_);
v___x_3085_ = v___x_3079_;
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_diag_3083_);
lean_inc(v_postponed_3082_);
lean_inc(v_zetaDeltaFVarIds_3081_);
lean_inc(v_mctx_3080_);
lean_dec(v___x_3079_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3087_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v___x_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_mctx_3080_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_zetaDeltaFVarIds_3081_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_postponed_3082_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v_diag_3083_);
v___x_3089_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_st_ref_set(v___y_3058_, v___x_3089_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
return v___x_3092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___boxed(lean_object* v_mod_3137_, lean_object* v_isMeta_3138_, lean_object* v_hint_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
uint8_t v_isMeta_boxed_3147_; lean_object* v_res_3148_; 
v_isMeta_boxed_3147_ = lean_unbox(v_isMeta_3138_);
v_res_3148_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(v_mod_3137_, v_isMeta_boxed_3147_, v_hint_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(lean_object* v___x_3149_, lean_object* v_declName_3150_, lean_object* v_as_3151_, size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v___x_3162_; 
v___x_3162_ = lean_usize_dec_lt(v_i_3153_, v_sz_3152_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_dec(v_declName_3150_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_b_3154_);
return v___x_3163_;
}
else
{
lean_object* v___x_3164_; lean_object* v_modules_3165_; lean_object* v___x_3166_; lean_object* v_a_3167_; lean_object* v___x_3168_; lean_object* v_toImport_3169_; lean_object* v_module_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; 
v___x_3164_ = l_Lean_Environment_header(v___x_3149_);
v_modules_3165_ = lean_ctor_get(v___x_3164_, 3);
lean_inc_ref(v_modules_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3167_ = lean_array_uget_borrowed(v_as_3151_, v_i_3153_);
v___x_3168_ = lean_array_get(v___x_3166_, v_modules_3165_, v_a_3167_);
lean_dec_ref(v_modules_3165_);
v_toImport_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc_ref(v_toImport_3169_);
lean_dec(v___x_3168_);
v_module_3170_ = lean_ctor_get(v_toImport_3169_, 0);
lean_inc(v_module_3170_);
lean_dec_ref(v_toImport_3169_);
v___x_3171_ = 0;
lean_inc(v_declName_3150_);
v___x_3172_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(v_module_3170_, v___x_3171_, v_declName_3150_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3173_; size_t v___x_3174_; size_t v___x_3175_; 
lean_dec_ref(v___x_3172_);
v___x_3173_ = lean_box(0);
v___x_3174_ = ((size_t)1ULL);
v___x_3175_ = lean_usize_add(v_i_3153_, v___x_3174_);
v_i_3153_ = v___x_3175_;
v_b_3154_ = v___x_3173_;
goto _start;
}
else
{
lean_dec(v_declName_3150_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1___boxed(lean_object* v___x_3177_, lean_object* v_declName_3178_, lean_object* v_as_3179_, lean_object* v_sz_3180_, lean_object* v_i_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
size_t v_sz_boxed_3190_; size_t v_i_boxed_3191_; lean_object* v_res_3192_; 
v_sz_boxed_3190_ = lean_unbox_usize(v_sz_3180_);
lean_dec(v_sz_3180_);
v_i_boxed_3191_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(v___x_3177_, v_declName_3178_, v_as_3179_, v_sz_boxed_3190_, v_i_boxed_3191_, v_b_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec_ref(v_as_3179_);
lean_dec_ref(v___x_3177_);
return v_res_3192_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__1));
v___x_3196_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__0));
v___x_3197_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3196_, v___x_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(lean_object* v_declName_3200_, uint8_t v_isMeta_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; lean_object* v_env_3213_; lean_object* v___y_3215_; lean_object* v___x_3228_; 
v___x_3209_ = lean_st_ref_get(v___y_3207_);
v_env_3213_ = lean_ctor_get(v___x_3209_, 0);
lean_inc_ref(v_env_3213_);
lean_dec(v___x_3209_);
v___x_3228_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3213_, v_declName_3200_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_dec_ref(v_env_3213_);
lean_dec(v_declName_3200_);
goto v___jp_3210_;
}
else
{
lean_object* v_val_3229_; lean_object* v___x_3230_; lean_object* v_modules_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v_val_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_val_3229_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = l_Lean_Environment_header(v_env_3213_);
v_modules_3231_ = lean_ctor_get(v___x_3230_, 3);
lean_inc_ref(v_modules_3231_);
lean_dec_ref(v___x_3230_);
v___x_3232_ = lean_array_get_size(v_modules_3231_);
v___x_3233_ = lean_nat_dec_lt(v_val_3229_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_dec_ref(v_modules_3231_);
lean_dec(v_val_3229_);
lean_dec_ref(v_env_3213_);
lean_dec(v_declName_3200_);
goto v___jp_3210_;
}
else
{
lean_object* v___x_3234_; lean_object* v_env_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___y_3239_; 
v___x_3234_ = lean_st_ref_get(v___y_3207_);
v_env_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc_ref(v_env_3235_);
lean_dec(v___x_3234_);
v___x_3236_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2);
v___x_3237_ = lean_array_fget(v_modules_3231_, v_val_3229_);
lean_dec(v_val_3229_);
lean_dec_ref(v_modules_3231_);
if (v_isMeta_3201_ == 0)
{
lean_dec_ref(v_env_3235_);
v___y_3239_ = v_isMeta_3201_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3250_; 
lean_inc(v_declName_3200_);
v___x_3250_ = l_Lean_isMarkedMeta(v_env_3235_, v_declName_3200_);
if (v___x_3250_ == 0)
{
v___y_3239_ = v_isMeta_3201_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3251_; 
v___x_3251_ = 0;
v___y_3239_ = v___x_3251_;
goto v___jp_3238_;
}
}
v___jp_3238_:
{
lean_object* v_toImport_3240_; lean_object* v_module_3241_; lean_object* v___x_3242_; 
v_toImport_3240_ = lean_ctor_get(v___x_3237_, 0);
lean_inc_ref(v_toImport_3240_);
lean_dec(v___x_3237_);
v_module_3241_ = lean_ctor_get(v_toImport_3240_, 0);
lean_inc(v_module_3241_);
lean_dec_ref(v_toImport_3240_);
lean_inc(v_declName_3200_);
v___x_3242_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(v_module_3241_, v___y_3239_, v_declName_3200_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec_ref(v___x_3242_);
v___x_3243_ = l_Lean_indirectModUseExt;
v___x_3244_ = lean_box(1);
v___x_3245_ = lean_box(0);
lean_inc_ref(v_env_3213_);
v___x_3246_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3236_, v___x_3243_, v_env_3213_, v___x_3244_, v___x_3245_);
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(v___x_3246_, v_declName_3200_);
lean_dec(v___x_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__3));
v___y_3215_ = v___x_3248_;
goto v___jp_3214_;
}
else
{
lean_object* v_val_3249_; 
v_val_3249_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_val_3249_);
lean_dec_ref(v___x_3247_);
v___y_3215_ = v_val_3249_;
goto v___jp_3214_;
}
}
else
{
lean_dec_ref(v_env_3213_);
lean_dec(v_declName_3200_);
return v___x_3242_;
}
}
}
}
v___jp_3210_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
v___jp_3214_:
{
lean_object* v___x_3216_; size_t v_sz_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3216_ = lean_box(0);
v_sz_3217_ = lean_array_size(v___y_3215_);
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(v_env_3213_, v_declName_3200_, v___y_3215_, v_sz_3217_, v___x_3218_, v___x_3216_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v_env_3213_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3219_, 0);
lean_dec(v_unused_3227_);
v___x_3221_ = v___x_3219_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v___x_3219_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3216_);
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3216_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___boxed(lean_object* v_declName_3252_, lean_object* v_isMeta_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v_isMeta_boxed_3261_; lean_object* v_res_3262_; 
v_isMeta_boxed_3261_ = lean_unbox(v_isMeta_3253_);
v_res_3262_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(v_declName_3252_, v_isMeta_boxed_3261_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3262_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0));
v___x_3265_ = l_Lean_stringToMessageData(v___x_3264_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2));
v___x_3268_ = l_Lean_stringToMessageData(v___x_3267_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_3276_ = l_Lean_MessageData_ofName(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3277_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8);
v___x_3278_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object* v_optConfig_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; uint8_t v_recover_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; uint8_t v___x_3330_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; 
v_recover_3324_ = lean_ctor_get_uint8(v_a_3284_, sizeof(void*)*1);
lean_inc(v_optConfig_3283_);
v___x_3325_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_3283_);
v___x_3326_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_3325_);
v___x_3327_ = lean_array_get_size(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_nat_dec_eq(v___x_3327_, v___x_3328_);
v___x_3330_ = 1;
if (v___x_3329_ == 0)
{
lean_object* v___x_3378_; lean_object* v_fileName_3379_; lean_object* v_fileMap_3380_; lean_object* v_options_3381_; lean_object* v_currRecDepth_3382_; lean_object* v_maxRecDepth_3383_; lean_object* v_ref_3384_; lean_object* v_currNamespace_3385_; lean_object* v_openDecls_3386_; lean_object* v_initHeartbeats_3387_; lean_object* v_maxHeartbeats_3388_; lean_object* v_quotContext_3389_; lean_object* v_currMacroScope_3390_; uint8_t v_diag_3391_; lean_object* v_cancelTk_x3f_3392_; uint8_t v_suppressElabErrors_3393_; lean_object* v_inheritedTraceOptions_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3415_; 
v___x_3378_ = lean_st_ref_get(v_a_3290_);
v_fileName_3379_ = lean_ctor_get(v_a_3289_, 0);
v_fileMap_3380_ = lean_ctor_get(v_a_3289_, 1);
v_options_3381_ = lean_ctor_get(v_a_3289_, 2);
v_currRecDepth_3382_ = lean_ctor_get(v_a_3289_, 3);
v_maxRecDepth_3383_ = lean_ctor_get(v_a_3289_, 4);
v_ref_3384_ = lean_ctor_get(v_a_3289_, 5);
v_currNamespace_3385_ = lean_ctor_get(v_a_3289_, 6);
v_openDecls_3386_ = lean_ctor_get(v_a_3289_, 7);
v_initHeartbeats_3387_ = lean_ctor_get(v_a_3289_, 8);
v_maxHeartbeats_3388_ = lean_ctor_get(v_a_3289_, 9);
v_quotContext_3389_ = lean_ctor_get(v_a_3289_, 10);
v_currMacroScope_3390_ = lean_ctor_get(v_a_3289_, 11);
v_diag_3391_ = lean_ctor_get_uint8(v_a_3289_, sizeof(void*)*14);
v_cancelTk_x3f_3392_ = lean_ctor_get(v_a_3289_, 12);
v_suppressElabErrors_3393_ = lean_ctor_get_uint8(v_a_3289_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3394_ = lean_ctor_get(v_a_3289_, 13);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_a_3289_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3396_ = v_a_3289_;
v_isShared_3397_ = v_isSharedCheck_3415_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_inheritedTraceOptions_3394_);
lean_inc(v_cancelTk_x3f_3392_);
lean_inc(v_currMacroScope_3390_);
lean_inc(v_quotContext_3389_);
lean_inc(v_maxHeartbeats_3388_);
lean_inc(v_initHeartbeats_3387_);
lean_inc(v_openDecls_3386_);
lean_inc(v_currNamespace_3385_);
lean_inc(v_ref_3384_);
lean_inc(v_maxRecDepth_3383_);
lean_inc(v_currRecDepth_3382_);
lean_inc(v_options_3381_);
lean_inc(v_fileMap_3380_);
lean_inc(v_fileName_3379_);
lean_dec(v_a_3289_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3415_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_env_3398_; lean_object* v_ref_3399_; lean_object* v___x_3401_; 
v_env_3398_ = lean_ctor_get(v___x_3378_, 0);
lean_inc_ref(v_env_3398_);
lean_dec(v___x_3378_);
v_ref_3399_ = l_Lean_replaceRef(v_optConfig_3283_, v_ref_3384_);
lean_dec(v_ref_3384_);
lean_dec(v_optConfig_3283_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 5, v_ref_3399_);
v___x_3401_ = v___x_3396_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_fileName_3379_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_fileMap_3380_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_options_3381_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_currRecDepth_3382_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_maxRecDepth_3383_);
lean_ctor_set(v_reuseFailAlloc_3414_, 5, v_ref_3399_);
lean_ctor_set(v_reuseFailAlloc_3414_, 6, v_currNamespace_3385_);
lean_ctor_set(v_reuseFailAlloc_3414_, 7, v_openDecls_3386_);
lean_ctor_set(v_reuseFailAlloc_3414_, 8, v_initHeartbeats_3387_);
lean_ctor_set(v_reuseFailAlloc_3414_, 9, v_maxHeartbeats_3388_);
lean_ctor_set(v_reuseFailAlloc_3414_, 10, v_quotContext_3389_);
lean_ctor_set(v_reuseFailAlloc_3414_, 11, v_currMacroScope_3390_);
lean_ctor_set(v_reuseFailAlloc_3414_, 12, v_cancelTk_x3f_3392_);
lean_ctor_set(v_reuseFailAlloc_3414_, 13, v_inheritedTraceOptions_3394_);
lean_ctor_set_uint8(v_reuseFailAlloc_3414_, sizeof(void*)*14, v_diag_3391_);
lean_ctor_set_uint8(v_reuseFailAlloc_3414_, sizeof(void*)*14 + 1, v_suppressElabErrors_3393_);
v___x_3401_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_3403_ = l_Lean_Environment_contains(v_env_3398_, v___x_3402_, v___x_3330_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v___x_3326_);
v___x_3404_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9);
v___x_3405_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3404_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v___x_3401_, v_a_3290_);
lean_dec(v_a_3290_);
lean_dec_ref(v___x_3401_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
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
else
{
v___y_3332_ = v_a_3285_;
v___y_3333_ = v_a_3286_;
v___y_3334_ = v_a_3287_;
v___y_3335_ = v_a_3288_;
v___y_3336_ = v___x_3401_;
v___y_3337_ = v_a_3290_;
goto v___jp_3331_;
}
}
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec_ref(v___x_3326_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_optConfig_3283_);
v___x_3416_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10));
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
v___jp_3292_:
{
if (v___y_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec_ref(v___y_3293_);
v___x_3303_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1);
v___x_3304_ = l_Lean_MessageData_ofExpr(v___y_3294_);
v___x_3305_ = l_Lean_indentD(v___x_3304_);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3303_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_Exception_toMessageData(v___y_3297_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3310_, v___y_3300_, v___y_3299_, v___y_3301_, v___y_3296_, v___y_3298_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3299_);
return v___x_3311_;
}
else
{
lean_dec_ref(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
return v___y_3293_;
}
}
v___jp_3312_:
{
lean_object* v___x_3320_; 
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc(v___y_3317_);
lean_inc_ref(v___y_3316_);
lean_inc_ref(v___y_3313_);
v___x_3320_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v___y_3313_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v___x_3320_;
}
else
{
lean_object* v_a_3321_; uint8_t v___x_3322_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
v___x_3322_ = l_Lean_Exception_isInterrupt(v_a_3321_);
if (v___x_3322_ == 0)
{
uint8_t v___x_3323_; 
lean_inc(v_a_3321_);
v___x_3323_ = l_Lean_Exception_isRuntime(v_a_3321_);
v___y_3293_ = v___x_3320_;
v___y_3294_ = v___y_3313_;
v___y_3295_ = v___y_3319_;
v___y_3296_ = v___y_3317_;
v___y_3297_ = v_a_3321_;
v___y_3298_ = v___y_3318_;
v___y_3299_ = v___y_3315_;
v___y_3300_ = v___y_3314_;
v___y_3301_ = v___y_3316_;
v___y_3302_ = v___x_3323_;
goto v___jp_3292_;
}
else
{
v___y_3293_ = v___x_3320_;
v___y_3294_ = v___y_3313_;
v___y_3295_ = v___y_3319_;
v___y_3296_ = v___y_3317_;
v___y_3297_ = v_a_3321_;
v___y_3298_ = v___y_3318_;
v___y_3299_ = v___y_3315_;
v___y_3300_ = v___y_3314_;
v___y_3301_ = v___y_3316_;
v___y_3302_ = v___x_3322_;
goto v___jp_3292_;
}
}
}
v___jp_3331_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_3339_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(v___x_3338_, v___x_3330_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; 
lean_dec_ref(v___x_3339_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
v___x_3340_ = l_Lean_Elab_Tactic_elabConfig(v_recover_3324_, v___x_3338_, v___x_3326_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3361_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3361_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3361_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
uint8_t v___x_3345_; 
v___x_3345_ = l_Lean_Expr_hasSyntheticSorry(v_a_3341_);
if (v___x_3345_ == 0)
{
uint8_t v___x_3346_; 
lean_del_object(v___x_3343_);
v___x_3346_ = l_Lean_Expr_hasSorry(v_a_3341_);
if (v___x_3346_ == 0)
{
v___y_3313_ = v_a_3341_;
v___y_3314_ = v___y_3332_;
v___y_3315_ = v___y_3333_;
v___y_3316_ = v___y_3334_;
v___y_3317_ = v___y_3335_;
v___y_3318_ = v___y_3336_;
v___y_3319_ = v___y_3337_;
goto v___jp_3312_;
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_a_3341_);
v___x_3347_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5);
v___x_3348_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3347_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
lean_dec(v_a_3341_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
v___x_3357_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3357_, 0, v___x_3329_);
lean_ctor_set_uint8(v___x_3357_, 1, v___x_3329_);
lean_ctor_set_uint8(v___x_3357_, 2, v___x_3330_);
lean_ctor_set_uint8(v___x_3357_, 3, v___x_3329_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 0, v___x_3357_);
v___x_3359_ = v___x_3343_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
v_a_3362_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3340_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3340_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
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
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___x_3326_);
v_a_3370_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3339_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3339_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object* v_optConfig_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_optConfig_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
lean_dec_ref(v_a_3419_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* v_optConfig_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_optConfig_3428_, v_a_3429_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* v_optConfig_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Elab_Tactic_elabDecideConfig(v_optConfig_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_3450_, v___y_3455_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2(v_cls_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2(lean_object* v_00_u03b2_3468_, lean_object* v_m_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(v_m_3469_, v_a_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3472_, lean_object* v_m_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2(v_00_u03b2_3472_, v_m_3473_, v_a_3474_);
lean_dec(v_a_3474_);
lean_dec_ref(v_m_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3476_, lean_object* v_x_3477_, lean_object* v_x_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_3477_, v_x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3480_, lean_object* v_x_3481_, lean_object* v_x_3482_){
_start:
{
uint8_t v_res_3483_; lean_object* v_r_3484_; 
v_res_3483_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1(v_00_u03b2_3480_, v_x_3481_, v_x_3482_);
lean_dec_ref(v_x_3482_);
v_r_3484_ = lean_box(v_res_3483_);
return v_r_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3(lean_object* v_cls_3485_, lean_object* v_msg_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___redArg(v_cls_3485_, v_msg_3486_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_3495_, lean_object* v_msg_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__3(v_cls_3495_, v_msg_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_3505_, lean_object* v_a_3506_, lean_object* v_x_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___redArg(v_a_3506_, v_x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_3509_, lean_object* v_a_3510_, lean_object* v_x_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__6(v_00_u03b2_3509_, v_a_3510_, v_x_3511_);
lean_dec(v_x_3511_);
lean_dec(v_a_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3513_, lean_object* v_x_3514_, size_t v_x_3515_, lean_object* v_x_3516_){
_start:
{
uint8_t v___x_3517_; 
v___x_3517_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3514_, v_x_3515_, v_x_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3518_, lean_object* v_x_3519_, lean_object* v_x_3520_, lean_object* v_x_3521_){
_start:
{
size_t v_x_11498__boxed_3522_; uint8_t v_res_3523_; lean_object* v_r_3524_; 
v_x_11498__boxed_3522_ = lean_unbox_usize(v_x_3520_);
lean_dec(v_x_3520_);
v_res_3523_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_3518_, v_x_3519_, v_x_11498__boxed_3522_, v_x_3521_);
lean_dec_ref(v_x_3521_);
v_r_3524_ = lean_box(v_res_3523_);
return v_r_3524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_3525_, lean_object* v_keys_3526_, lean_object* v_vals_3527_, lean_object* v_heq_3528_, lean_object* v_i_3529_, lean_object* v_k_3530_){
_start:
{
uint8_t v___x_3531_; 
v___x_3531_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___redArg(v_keys_3526_, v_i_3529_, v_k_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_3532_, lean_object* v_keys_3533_, lean_object* v_vals_3534_, lean_object* v_heq_3535_, lean_object* v_i_3536_, lean_object* v_k_3537_){
_start:
{
uint8_t v_res_3538_; lean_object* v_r_3539_; 
v_res_3538_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_3532_, v_keys_3533_, v_vals_3534_, v_heq_3535_, v_i_3536_, v_k_3537_);
lean_dec_ref(v_k_3537_);
lean_dec_ref(v_vals_3534_);
lean_dec_ref(v_keys_3533_);
v_r_3539_ = lean_box(v_res_3538_);
return v_r_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* v_stx_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = l_Lean_Syntax_getArg(v_stx_3543_, v___x_3553_);
lean_inc(v_a_3551_);
lean_inc_ref(v_a_3550_);
lean_inc(v_a_3549_);
lean_inc_ref(v_a_3548_);
lean_inc(v_a_3547_);
lean_inc_ref(v_a_3546_);
v___x_3555_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3554_, v_a_3544_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__1));
v___x_3558_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3557_, v_a_3556_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3556_);
return v___x_3558_;
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
v_a_3559_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3555_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3555_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object* v_stx_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Elab_Tactic_evalDecide(v_stx_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_stx_3567_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3591_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3592_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0));
v___x_3593_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3594_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
v___x_3595_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3591_, v___x_3592_, v___x_3593_, v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3625_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6));
v___x_3626_ = l_Lean_addBuiltinDeclarationRanges(v___x_3624_, v___x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* v_stx_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_unsigned_to_nat(1u);
v___x_3643_ = l_Lean_Syntax_getArg(v_stx_3632_, v___x_3642_);
lean_inc(v_a_3640_);
lean_inc_ref(v_a_3639_);
lean_inc(v_a_3638_);
lean_inc_ref(v_a_3637_);
lean_inc(v_a_3636_);
lean_inc_ref(v_a_3635_);
v___x_3644_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3643_, v_a_3633_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; uint8_t v_kernel_3646_; uint8_t v_zetaReduce_3647_; uint8_t v_revert_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3658_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
v_kernel_3646_ = lean_ctor_get_uint8(v_a_3645_, 0);
v_zetaReduce_3647_ = lean_ctor_get_uint8(v_a_3645_, 2);
v_revert_3648_ = lean_ctor_get_uint8(v_a_3645_, 3);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_a_3645_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3650_ = v_a_3645_;
v_isShared_3651_ = v_isSharedCheck_3658_;
goto v_resetjp_3649_;
}
else
{
lean_dec(v_a_3645_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3658_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
uint8_t v___x_3652_; lean_object* v___x_3654_; 
v___x_3652_ = 1;
if (v_isShared_3651_ == 0)
{
v___x_3654_ = v___x_3650_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, 0, v_kernel_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, 2, v_zetaReduce_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, 3, v_revert_3648_);
v___x_3654_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_ctor_set_uint8(v___x_3654_, 1, v___x_3652_);
v___x_3655_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___closed__1));
v___x_3656_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3655_, v___x_3654_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
lean_dec_ref(v___x_3654_);
return v___x_3656_;
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
v_a_3659_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3644_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3644_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object* v_stx_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_Elab_Tactic_evalNativeDecide(v_stx_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
lean_dec(v_stx_3667_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3691_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3692_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1));
v___x_3693_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
v___x_3695_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3691_, v___x_3692_, v___x_3693_, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3725_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6));
v___x_3726_ = l_Lean_addBuiltinDeclarationRanges(v___x_3724_, v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
return v_res_3728_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Decide(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
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
lean_object* initialize_Lean_Meta_Native(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Decide(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
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
