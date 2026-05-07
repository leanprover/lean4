// Lean compiler output
// Module: Lean.Elab.Tactic.Decide
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Meta.Tactic.Cleanup import Lean.Meta.Native import Lean.Elab.Tactic.ElabTerm
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
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_Lean_diagnostics;
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
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__17_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l_Lean_Elab_Tactic_evalDecide___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 229, 81, 15, 25, 144, 49, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalNativeDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2(void){
_start:
{
lean_object* v___x_397_; lean_object* v_dummy_398_; 
v___x_397_ = lean_box(0);
v_dummy_398_ = l_Lean_Expr_sort___override(v___x_397_);
return v_dummy_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_fileName_405_; lean_object* v_fileMap_406_; lean_object* v_options_407_; lean_object* v_currRecDepth_408_; lean_object* v_maxRecDepth_409_; lean_object* v_ref_410_; lean_object* v_currNamespace_411_; lean_object* v_openDecls_412_; lean_object* v_initHeartbeats_413_; lean_object* v_maxHeartbeats_414_; lean_object* v_quotContext_415_; lean_object* v_currMacroScope_416_; uint8_t v_diag_417_; lean_object* v_cancelTk_x3f_418_; uint8_t v_suppressElabErrors_419_; lean_object* v_inheritedTraceOptions_420_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_fileName_405_ = lean_ctor_get(v_a_402_, 0);
lean_inc_ref(v_fileName_405_);
v_fileMap_406_ = lean_ctor_get(v_a_402_, 1);
lean_inc_ref(v_fileMap_406_);
v_options_407_ = lean_ctor_get(v_a_402_, 2);
lean_inc_ref(v_options_407_);
v_currRecDepth_408_ = lean_ctor_get(v_a_402_, 3);
lean_inc(v_currRecDepth_408_);
v_maxRecDepth_409_ = lean_ctor_get(v_a_402_, 4);
lean_inc(v_maxRecDepth_409_);
v_ref_410_ = lean_ctor_get(v_a_402_, 5);
lean_inc(v_ref_410_);
v_currNamespace_411_ = lean_ctor_get(v_a_402_, 6);
lean_inc(v_currNamespace_411_);
v_openDecls_412_ = lean_ctor_get(v_a_402_, 7);
lean_inc(v_openDecls_412_);
v_initHeartbeats_413_ = lean_ctor_get(v_a_402_, 8);
lean_inc(v_initHeartbeats_413_);
v_maxHeartbeats_414_ = lean_ctor_get(v_a_402_, 9);
lean_inc(v_maxHeartbeats_414_);
v_quotContext_415_ = lean_ctor_get(v_a_402_, 10);
lean_inc(v_quotContext_415_);
v_currMacroScope_416_ = lean_ctor_get(v_a_402_, 11);
lean_inc(v_currMacroScope_416_);
v_diag_417_ = lean_ctor_get_uint8(v_a_402_, sizeof(void*)*14);
v_cancelTk_x3f_418_ = lean_ctor_get(v_a_402_, 12);
lean_inc(v_cancelTk_x3f_418_);
v_suppressElabErrors_419_ = lean_ctor_get_uint8(v_a_402_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_420_ = lean_ctor_get(v_a_402_, 13);
lean_inc_ref(v_inheritedTraceOptions_420_);
lean_dec_ref(v_a_402_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v_maxRecDepth_409_, v___x_487_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_eq(v_currRecDepth_408_, v_maxRecDepth_409_);
if (v___x_489_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v_inheritedTraceOptions_420_);
lean_dec(v_cancelTk_x3f_418_);
lean_dec(v_currMacroScope_416_);
lean_dec(v_quotContext_415_);
lean_dec(v_maxHeartbeats_414_);
lean_dec(v_initHeartbeats_413_);
lean_dec(v_openDecls_412_);
lean_dec(v_currNamespace_411_);
lean_dec(v_maxRecDepth_409_);
lean_dec(v_currRecDepth_408_);
lean_dec_ref(v_options_407_);
lean_dec_ref(v_fileMap_406_);
lean_dec_ref(v_fileName_405_);
lean_dec_ref(v_inst_399_);
v___x_490_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_410_);
return v___x_490_;
}
}
else
{
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_currRecDepth_408_, v___x_422_);
lean_dec(v_currRecDepth_408_);
v___x_424_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_424_, 0, v_fileName_405_);
lean_ctor_set(v___x_424_, 1, v_fileMap_406_);
lean_ctor_set(v___x_424_, 2, v_options_407_);
lean_ctor_set(v___x_424_, 3, v___x_423_);
lean_ctor_set(v___x_424_, 4, v_maxRecDepth_409_);
lean_ctor_set(v___x_424_, 5, v_ref_410_);
lean_ctor_set(v___x_424_, 6, v_currNamespace_411_);
lean_ctor_set(v___x_424_, 7, v_openDecls_412_);
lean_ctor_set(v___x_424_, 8, v_initHeartbeats_413_);
lean_ctor_set(v___x_424_, 9, v_maxHeartbeats_414_);
lean_ctor_set(v___x_424_, 10, v_quotContext_415_);
lean_ctor_set(v___x_424_, 11, v_currMacroScope_416_);
lean_ctor_set(v___x_424_, 12, v_cancelTk_x3f_418_);
lean_ctor_set(v___x_424_, 13, v_inheritedTraceOptions_420_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*14, v_diag_417_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*14 + 1, v_suppressElabErrors_419_);
lean_inc(v_a_403_);
lean_inc_ref(v___x_424_);
lean_inc(v_a_401_);
lean_inc_ref(v_a_400_);
v___x_425_ = lean_whnf(v_inst_399_, v_a_400_, v_a_401_, v___x_424_, v_a_403_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
v___x_427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1));
v___x_428_ = lean_unsigned_to_nat(5u);
v___x_429_ = l_Lean_Expr_isAppOfArity(v_a_426_, v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Expr_getAppFn(v_a_426_);
if (lean_obj_tag(v___x_430_) == 4)
{
lean_object* v_declName_431_; lean_object* v___x_432_; 
lean_dec_ref(v___x_425_);
v_declName_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_declName_431_);
lean_dec_ref(v___x_430_);
v___x_432_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_431_, v_a_403_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_476_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_476_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_476_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_476_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
if (lean_obj_tag(v_a_433_) == 1)
{
lean_object* v_val_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_val_437_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_val_437_);
lean_dec_ref(v_a_433_);
v___x_438_ = l_Lean_Expr_getAppNumArgs(v_a_426_);
v___x_439_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_437_);
v___x_440_ = lean_nat_dec_eq(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v___x_439_);
lean_dec(v___x_438_);
lean_dec(v_val_437_);
lean_dec_ref(v___x_424_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_a_426_);
v___x_442_ = v___x_435_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_426_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v_numDiscrs_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_dummy_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_del_object(v___x_435_);
v_numDiscrs_444_ = lean_ctor_get(v_val_437_, 1);
lean_inc(v_numDiscrs_444_);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1));
v_dummy_447_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2);
lean_inc(v___x_438_);
v___x_448_ = lean_mk_array(v___x_438_, v_dummy_447_);
v___x_449_ = lean_nat_sub(v___x_438_, v___x_422_);
lean_inc(v_a_426_);
v___x_450_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_426_, v___x_448_, v___x_449_);
v___x_451_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_numDiscrs_444_, v_val_437_, v___x_450_, v___x_429_, v___x_438_, v___x_439_, v___x_445_, v___x_446_, v_a_400_, v_a_401_, v___x_424_, v_a_403_);
lean_dec_ref(v___x_424_);
lean_dec(v___x_439_);
lean_dec(v___x_438_);
lean_dec_ref(v___x_450_);
lean_dec(v_val_437_);
lean_dec(v_numDiscrs_444_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_464_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_464_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_464_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_464_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_fst_456_; 
v_fst_456_ = lean_ctor_get(v_a_452_, 0);
lean_inc(v_fst_456_);
lean_dec(v_a_452_);
if (lean_obj_tag(v_fst_456_) == 0)
{
lean_object* v___x_458_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_a_426_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_426_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v_val_460_; lean_object* v___x_462_; 
lean_dec(v_a_426_);
v_val_460_ = lean_ctor_get(v_fst_456_, 0);
lean_inc(v_val_460_);
lean_dec_ref(v_fst_456_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_val_460_);
v___x_462_ = v___x_454_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_val_460_);
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
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_a_426_);
v_a_465_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_451_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_451_);
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
lean_object* v___x_474_; 
lean_dec(v_a_433_);
lean_dec_ref(v___x_424_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_a_426_);
v___x_474_ = v___x_435_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_426_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_a_426_);
lean_dec_ref(v___x_424_);
v_a_477_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_432_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_432_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
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
else
{
lean_dec_ref(v___x_430_);
lean_dec(v_a_426_);
lean_dec_ref(v___x_424_);
return v___x_425_;
}
}
else
{
lean_object* v___x_485_; 
lean_dec_ref(v___x_425_);
v___x_485_ = l_Lean_Expr_appArg_x21(v_a_426_);
lean_dec(v_a_426_);
v_inst_399_ = v___x_485_;
v_a_402_ = v___x_424_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_424_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(lean_object* v_upperBound_491_, lean_object* v_val_492_, lean_object* v___x_493_, uint8_t v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_a_505_; uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_lt(v_a_497_, v_upperBound_491_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v_a_497_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_b_498_);
return v___x_510_;
}
else
{
lean_object* v_numParams_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v_b_498_);
v_numParams_511_ = lean_ctor_get(v_val_492_, 0);
v___x_512_ = l_Lean_instInhabitedExpr;
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_numParams_511_, v___x_513_);
v___x_515_ = lean_nat_add(v___x_514_, v_a_497_);
lean_dec(v___x_514_);
v___x_516_ = lean_array_get_borrowed(v___x_512_, v___x_493_, v___x_515_);
lean_dec(v___x_515_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___x_516_);
v___x_517_ = lean_infer_type(v___x_516_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v___x_519_ = l_Lean_Meta_isClass_x3f(v_a_518_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_519_);
v___x_521_ = lean_box(0);
v___x_522_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1));
v___x_523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3));
v___x_524_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_a_520_, v___x_523_);
lean_dec(v_a_520_);
if (v___x_524_ == 0)
{
v_a_505_ = v___x_522_;
goto v___jp_504_;
}
else
{
lean_object* v___x_525_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___x_516_);
v___x_525_ = lean_whnf(v___x_516_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint8_t v___y_528_; uint8_t v___y_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
v___x_550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5));
v___x_551_ = l_Lean_Expr_isAppOf(v_a_526_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7));
v___x_553_ = l_Lean_Expr_isAppOf(v_a_526_, v___x_552_);
v___y_549_ = v___x_553_;
goto v___jp_548_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = lean_nat_dec_eq(v___x_495_, v___x_496_);
v___y_549_ = v___x_554_;
goto v___jp_548_;
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
lean_dec(v_a_526_);
v_a_505_ = v___x_522_;
goto v___jp_504_;
}
else
{
lean_object* v___x_529_; 
lean_dec(v_a_497_);
lean_inc_ref(v___y_501_);
v___x_529_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_526_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_a_530_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_521_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_535_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_529_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_529_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
v___jp_548_:
{
if (v___y_549_ == 0)
{
v___y_528_ = v___x_524_;
goto v___jp_527_;
}
else
{
v___y_528_ = v___x_494_;
goto v___jp_527_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_497_);
v_a_555_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_525_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_525_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_a_497_);
v_a_563_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_519_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_519_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
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
lean_dec(v_a_497_);
v_a_571_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_517_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_517_);
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
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_a_497_, v___x_506_);
lean_dec(v_a_497_);
lean_inc_ref(v_a_505_);
v_a_497_ = v___x_507_;
v_b_498_ = v_a_505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(lean_object* v_upperBound_579_, lean_object* v_val_580_, lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v___x_583_, lean_object* v___x_584_, lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___x_7093__boxed_592_; lean_object* v_res_593_; 
v___x_7093__boxed_592_ = lean_unbox(v___x_582_);
v_res_593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_upperBound_579_, v_val_580_, v___x_581_, v___x_7093__boxed_592_, v___x_583_, v___x_584_, v_a_585_, v_b_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___x_584_);
lean_dec(v___x_583_);
lean_dec_ref(v___x_581_);
lean_dec_ref(v_val_580_);
lean_dec(v_upperBound_579_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(lean_object* v_inst_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_inst_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(lean_object* v_upperBound_601_, lean_object* v_val_602_, lean_object* v___x_603_, uint8_t v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v_inst_607_, lean_object* v_R_608_, lean_object* v_a_609_, lean_object* v_b_610_, lean_object* v_c_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_upperBound_601_, v_val_602_, v___x_603_, v___x_604_, v___x_605_, v___x_606_, v_a_609_, v_b_610_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(lean_object* v_upperBound_618_, lean_object* v_val_619_, lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_inst_624_, lean_object* v_R_625_, lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_c_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_7439__boxed_634_; lean_object* v_res_635_; 
v___x_7439__boxed_634_ = lean_unbox(v___x_621_);
v_res_635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(v_upperBound_618_, v_val_619_, v___x_620_, v___x_7439__boxed_634_, v___x_622_, v___x_623_, v_inst_624_, v_R_625_, v_a_626_, v_b_627_, v_c_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___x_623_);
lean_dec(v___x_622_);
lean_dec_ref(v___x_620_);
lean_dec_ref(v_val_619_);
lean_dec(v_upperBound_618_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_ref_642_; lean_object* v___x_643_; lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
v_ref_642_ = lean_ctor_get(v___y_639_, 5);
v___x_643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_652_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
lean_inc(v_ref_642_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_ref_642_);
lean_ctor_set(v___x_648_, 1, v_a_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 1);
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_659_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(0);
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1));
v___x_665_ = l_Lean_mkConst(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore(lean_object* v_tacticName_675_, lean_object* v_expectedType_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; 
lean_inc_ref(v_expectedType_676_);
v___x_686_ = l_Lean_Meta_mkDecide(v_expectedType_676_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_726_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_726_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_726_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_726_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_ref_691_; lean_object* v___x_693_; 
v_ref_691_ = lean_ctor_get(v_a_683_, 5);
lean_inc(v_ref_691_);
if (v_isShared_690_ == 0)
{
lean_ctor_set_tag(v___x_689_, 1);
lean_ctor_set(v___x_689_, 0, v_ref_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_ref_691_);
v___x_693_ = v_reuseFailAlloc_725_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; 
lean_inc(v_a_687_);
lean_inc(v_tacticName_675_);
v___x_694_ = l_Lean_Meta_nativeEqTrue(v_tacticName_675_, v_a_687_, v___x_693_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec_ref(v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_716_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_716_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_716_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_716_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
if (lean_obj_tag(v_a_695_) == 0)
{
lean_object* v_prf_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec(v_tacticName_675_);
v_prf_699_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_prf_699_);
lean_dec_ref(v_a_695_);
v___x_700_ = l_Lean_Expr_appArg_x21(v_a_687_);
lean_dec(v_a_687_);
v___x_701_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2);
v___x_702_ = l_Lean_mkApp3(v___x_701_, v_expectedType_676_, v___x_700_, v_prf_699_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_702_);
v___x_704_ = v___x_697_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_del_object(v___x_697_);
lean_dec(v_a_687_);
v___x_706_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_707_ = l_Lean_MessageData_ofName(v_tacticName_675_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_indentExpr(v_expectedType_676_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_714_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
return v___x_715_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_687_);
lean_dec_ref(v_expectedType_676_);
lean_dec(v_tacticName_675_);
v_a_717_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_694_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_694_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_676_);
lean_dec(v_tacticName_675_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(lean_object* v_tacticName_727_, lean_object* v_expectedType_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_727_, v_expectedType_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(lean_object* v_00_u03b1_739_, lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v_msg_740_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(lean_object* v_00_u03b1_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(v_00_u03b1_751_, v_msg_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(lean_object* v_opts_763_, lean_object* v_opt_764_){
_start:
{
lean_object* v_name_765_; lean_object* v_defValue_766_; lean_object* v_map_767_; lean_object* v___x_768_; 
v_name_765_ = lean_ctor_get(v_opt_764_, 0);
v_defValue_766_ = lean_ctor_get(v_opt_764_, 1);
v_map_767_ = lean_ctor_get(v_opts_763_, 0);
v___x_768_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_767_, v_name_765_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_inc(v_defValue_766_);
return v_defValue_766_;
}
else
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref(v___x_768_);
if (lean_obj_tag(v_val_769_) == 3)
{
lean_object* v_v_770_; 
v_v_770_ = lean_ctor_get(v_val_769_, 0);
lean_inc(v_v_770_);
lean_dec_ref(v_val_769_);
return v_v_770_;
}
else
{
lean_dec(v_val_769_);
lean_inc(v_defValue_766_);
return v_defValue_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(lean_object* v_opts_771_, lean_object* v_opt_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_opts_771_, v_opt_772_);
lean_dec_ref(v_opt_772_);
lean_dec_ref(v_opts_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_saveState___redArg(v___y_776_, v___y_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_r_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
v_r_782_ = lean_apply_5(v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, lean_box(0));
if (lean_obj_tag(v_r_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v_r_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v_r_782_);
v___x_784_ = l_Lean_Meta_SavedState_restore___redArg(v_a_781_, v___y_776_, v___y_778_);
lean_dec(v_a_781_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_792_);
v___x_786_ = v___x_784_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_dec(v___x_784_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_a_783_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_783_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec(v_a_783_);
v_a_793_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_784_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v_r_782_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v_r_782_);
v___x_802_ = l_Lean_Meta_SavedState_restore___redArg(v_a_781_, v___y_776_, v___y_778_);
lean_dec(v_a_781_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_810_);
v___x_804_ = v___x_802_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_dec(v___x_802_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 1);
lean_ctor_set(v___x_804_, 0, v_a_801_);
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_801_);
v_a_811_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_802_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_802_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_x_774_);
v_a_819_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_780_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_780_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(lean_object* v_00_u03b1_834_, lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_x_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(lean_object* v_00_u03b1_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_00_u03b1_842_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(lean_object* v_cs_850_, lean_object* v_n_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_array_push(v_cs_850_, v_n_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(lean_object* v_cs_854_, lean_object* v_n_855_, lean_object* v_x_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(v_cs_854_, v_n_855_, v_x_856_);
lean_dec(v_x_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object* v_o_861_, lean_object* v_k_862_, uint8_t v_v_863_){
_start:
{
lean_object* v_map_864_; uint8_t v_hasTrace_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_879_; 
v_map_864_ = lean_ctor_get(v_o_861_, 0);
v_hasTrace_865_ = lean_ctor_get_uint8(v_o_861_, sizeof(void*)*1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_o_861_);
if (v_isSharedCheck_879_ == 0)
{
v___x_867_ = v_o_861_;
v_isShared_868_ = v_isSharedCheck_879_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_map_864_);
lean_dec(v_o_861_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_879_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_869_, 0, v_v_863_);
lean_inc(v_k_862_);
v___x_870_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_862_, v___x_869_, v_map_864_);
if (v_hasTrace_865_ == 0)
{
lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_874_; 
v___x_871_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1));
v___x_872_ = l_Lean_Name_isPrefixOf(v___x_871_, v_k_862_);
lean_dec(v_k_862_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_874_ = v___x_867_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_870_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*1, v___x_872_);
return v___x_874_;
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v_k_862_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_878_, sizeof(void*)*1, v_hasTrace_865_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object* v_o_880_, lean_object* v_k_881_, lean_object* v_v_882_){
_start:
{
uint8_t v_v_boxed_883_; lean_object* v_res_884_; 
v_v_boxed_883_ = lean_unbox(v_v_882_);
v_res_884_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_o_880_, v_k_881_, v_v_boxed_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object* v_opts_885_, lean_object* v_opt_886_, uint8_t v_val_887_){
_start:
{
lean_object* v_name_888_; lean_object* v___x_889_; 
v_name_888_ = lean_ctor_get(v_opt_886_, 0);
lean_inc(v_name_888_);
lean_dec_ref(v_opt_886_);
v___x_889_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_opts_885_, v_name_888_, v_val_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object* v_opts_890_, lean_object* v_opt_891_, lean_object* v_val_892_){
_start:
{
uint8_t v_val_boxed_893_; lean_object* v_res_894_; 
v_val_boxed_893_ = lean_unbox(v_val_892_);
v_res_894_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_opts_890_, v_opt_891_, v_val_boxed_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(lean_object* v_f_895_, lean_object* v_keys_896_, lean_object* v_vals_897_, lean_object* v_i_898_, lean_object* v_acc_899_){
_start:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_array_get_size(v_keys_896_);
v___x_901_ = lean_nat_dec_lt(v_i_898_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec(v_i_898_);
lean_dec(v_f_895_);
return v_acc_899_;
}
else
{
lean_object* v_k_902_; lean_object* v_v_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_k_902_ = lean_array_fget_borrowed(v_keys_896_, v_i_898_);
v_v_903_ = lean_array_fget_borrowed(v_vals_897_, v_i_898_);
lean_inc(v_f_895_);
lean_inc(v_v_903_);
lean_inc(v_k_902_);
v___x_904_ = lean_apply_3(v_f_895_, v_acc_899_, v_k_902_, v_v_903_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_i_898_, v___x_905_);
lean_dec(v_i_898_);
v_i_898_ = v___x_906_;
v_acc_899_ = v___x_904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg___boxed(lean_object* v_f_908_, lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_i_911_, lean_object* v_acc_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_908_, v_keys_909_, v_vals_910_, v_i_911_, v_acc_912_);
lean_dec_ref(v_vals_910_);
lean_dec_ref(v_keys_909_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(lean_object* v_f_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_es_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_es_917_ = lean_ctor_get(v_x_915_, 0);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_array_get_size(v_es_917_);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_dec(v_f_914_);
return v_x_916_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_le(v___x_919_, v___x_919_);
if (v___x_921_ == 0)
{
if (v___x_920_ == 0)
{
lean_dec(v_f_914_);
return v_x_916_;
}
else
{
size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((size_t)0ULL);
v___x_923_ = lean_usize_of_nat(v___x_919_);
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_914_, v_es_917_, v___x_922_, v___x_923_, v_x_916_);
return v___x_924_;
}
}
else
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_919_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_914_, v_es_917_, v___x_925_, v___x_926_, v_x_916_);
return v___x_927_;
}
}
}
else
{
lean_object* v_ks_928_; lean_object* v_vs_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_ks_928_ = lean_ctor_get(v_x_915_, 0);
v_vs_929_ = lean_ctor_get(v_x_915_, 1);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_914_, v_ks_928_, v_vs_929_, v___x_930_, v_x_916_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(lean_object* v_f_932_, lean_object* v_as_933_, size_t v_i_934_, size_t v_stop_935_, lean_object* v_b_936_){
_start:
{
lean_object* v___y_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_eq(v_i_934_, v_stop_935_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_array_uget_borrowed(v_as_933_, v_i_934_);
switch(lean_obj_tag(v___x_943_))
{
case 0:
{
lean_object* v_key_944_; lean_object* v_val_945_; lean_object* v___x_946_; 
v_key_944_ = lean_ctor_get(v___x_943_, 0);
v_val_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_f_932_);
lean_inc(v_val_945_);
lean_inc(v_key_944_);
v___x_946_ = lean_apply_3(v_f_932_, v_b_936_, v_key_944_, v_val_945_);
v___y_938_ = v___x_946_;
goto v___jp_937_;
}
case 1:
{
lean_object* v_node_947_; lean_object* v___x_948_; 
v_node_947_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_f_932_);
v___x_948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_932_, v_node_947_, v_b_936_);
v___y_938_ = v___x_948_;
goto v___jp_937_;
}
default: 
{
v___y_938_ = v_b_936_;
goto v___jp_937_;
}
}
}
else
{
lean_dec(v_f_932_);
return v_b_936_;
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_934_, v___x_939_);
v_i_934_ = v___x_940_;
v_b_936_ = v___y_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_f_949_, lean_object* v_as_950_, lean_object* v_i_951_, lean_object* v_stop_952_, lean_object* v_b_953_){
_start:
{
size_t v_i_boxed_954_; size_t v_stop_boxed_955_; lean_object* v_res_956_; 
v_i_boxed_954_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_stop_boxed_955_ = lean_unbox_usize(v_stop_952_);
lean_dec(v_stop_952_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_949_, v_as_950_, v_i_boxed_954_, v_stop_boxed_955_, v_b_953_);
lean_dec_ref(v_as_950_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_f_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_957_, v_x_958_, v_x_959_);
lean_dec_ref(v_x_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0(lean_object* v_f_961_, lean_object* v_x1_962_, lean_object* v_x2_963_, lean_object* v_x3_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_apply_3(v_f_961_, v_x1_962_, v_x2_963_, v_x3_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(lean_object* v_map_966_, lean_object* v_f_967_, lean_object* v_init_968_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; 
v___f_969_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_969_, 0, v_f_967_);
v___x_970_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v___f_969_, v_map_966_, v_init_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___boxed(lean_object* v_map_971_, lean_object* v_f_972_, lean_object* v_init_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_971_, v_f_972_, v_init_973_);
lean_dec_ref(v_map_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(lean_object* v_hi_975_, lean_object* v_pivot_976_, lean_object* v_as_977_, lean_object* v_i_978_, lean_object* v_k_979_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = lean_nat_dec_lt(v_k_979_, v_hi_975_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v_k_979_);
v___x_981_ = lean_array_fswap(v_as_977_, v_i_978_, v_hi_975_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_i_978_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = lean_array_fget_borrowed(v_as_977_, v_k_979_);
v___x_984_ = l_Lean_Name_lt(v___x_983_, v_pivot_976_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_k_979_, v___x_985_);
lean_dec(v_k_979_);
v_k_979_ = v___x_986_;
goto _start;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_array_fswap(v_as_977_, v_i_978_, v_k_979_);
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_add(v_i_978_, v___x_989_);
lean_dec(v_i_978_);
v___x_991_ = lean_nat_add(v_k_979_, v___x_989_);
lean_dec(v_k_979_);
v_as_977_ = v___x_988_;
v_i_978_ = v___x_990_;
v_k_979_ = v___x_991_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg___boxed(lean_object* v_hi_993_, lean_object* v_pivot_994_, lean_object* v_as_995_, lean_object* v_i_996_, lean_object* v_k_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(v_hi_993_, v_pivot_994_, v_as_995_, v_i_996_, v_k_997_);
lean_dec(v_pivot_994_);
lean_dec(v_hi_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(lean_object* v_n_999_, lean_object* v_as_1000_, lean_object* v_lo_1001_, lean_object* v_hi_1002_){
_start:
{
lean_object* v___y_1004_; uint8_t v___x_1014_; 
v___x_1014_ = lean_nat_dec_lt(v_lo_1001_, v_hi_1002_);
if (v___x_1014_ == 0)
{
lean_dec(v_lo_1001_);
return v_as_1000_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_mid_1017_; lean_object* v___y_1019_; lean_object* v___y_1025_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1015_ = lean_nat_add(v_lo_1001_, v_hi_1002_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v_mid_1017_ = lean_nat_shiftr(v___x_1015_, v___x_1016_);
lean_dec(v___x_1015_);
v___x_1030_ = lean_array_fget_borrowed(v_as_1000_, v_mid_1017_);
v___x_1031_ = lean_array_fget_borrowed(v_as_1000_, v_lo_1001_);
v___x_1032_ = l_Lean_Name_lt(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
v___y_1025_ = v_as_1000_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_array_fswap(v_as_1000_, v_lo_1001_, v_mid_1017_);
v___y_1025_ = v___x_1033_;
goto v___jp_1024_;
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1020_ = lean_array_fget_borrowed(v___y_1019_, v_mid_1017_);
v___x_1021_ = lean_array_fget_borrowed(v___y_1019_, v_hi_1002_);
v___x_1022_ = l_Lean_Name_lt(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v_mid_1017_);
v___y_1004_ = v___y_1019_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_array_fswap(v___y_1019_, v_mid_1017_, v_hi_1002_);
lean_dec(v_mid_1017_);
v___y_1004_ = v___x_1023_;
goto v___jp_1003_;
}
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_array_fget_borrowed(v___y_1025_, v_hi_1002_);
v___x_1027_ = lean_array_fget_borrowed(v___y_1025_, v_lo_1001_);
v___x_1028_ = l_Lean_Name_lt(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
v___y_1019_ = v___y_1025_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_array_fswap(v___y_1025_, v_lo_1001_, v_hi_1002_);
v___y_1019_ = v___x_1029_;
goto v___jp_1018_;
}
}
}
v___jp_1003_:
{
lean_object* v_pivot_1005_; lean_object* v___x_1006_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; uint8_t v___x_1009_; 
v_pivot_1005_ = lean_array_fget(v___y_1004_, v_hi_1002_);
lean_inc_n(v_lo_1001_, 2);
v___x_1006_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(v_hi_1002_, v_pivot_1005_, v___y_1004_, v_lo_1001_, v_lo_1001_);
lean_dec(v_pivot_1005_);
v_fst_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_fst_1007_);
v_snd_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_snd_1008_);
lean_dec_ref(v___x_1006_);
v___x_1009_ = lean_nat_dec_le(v_hi_1002_, v_fst_1007_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_999_, v_snd_1008_, v_lo_1001_, v_fst_1007_);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_add(v_fst_1007_, v___x_1011_);
lean_dec(v_fst_1007_);
v_as_1000_ = v___x_1010_;
v_lo_1001_ = v___x_1012_;
goto _start;
}
else
{
lean_dec(v_fst_1007_);
lean_dec(v_lo_1001_);
return v_snd_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(lean_object* v_n_1034_, lean_object* v_as_1035_, lean_object* v_lo_1036_, lean_object* v_hi_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_1034_, v_as_1035_, v_lo_1036_, v_hi_1037_);
lean_dec(v_hi_1037_);
lean_dec(v_n_1034_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
if (lean_obj_tag(v_a_1039_) == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = l_List_reverse___redArg(v_a_1040_);
return v___x_1041_;
}
else
{
lean_object* v_head_1042_; lean_object* v_tail_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1052_; 
v_head_1042_ = lean_ctor_get(v_a_1039_, 0);
v_tail_1043_ = lean_ctor_get(v_a_1039_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_1039_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1045_ = v_a_1039_;
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_tail_1043_);
lean_inc(v_head_1042_);
lean_dec(v_a_1039_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = l_Lean_mkLevelParam(v_head_1042_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v_a_1040_);
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_a_1040_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
v_a_1039_ = v_tail_1043_;
v_a_1040_ = v___x_1049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_ref_1059_; lean_object* v___x_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_ref_1059_ = lean_ctor_get(v___y_1056_, 5);
v___x_1060_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_inc(v_ref_1059_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_ref_1059_);
lean_ctor_set(v___x_1065_, 1, v_a_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg___boxed(lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v_msg_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(lean_object* v_ref_1077_, lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_fileName_1084_; lean_object* v_fileMap_1085_; lean_object* v_options_1086_; lean_object* v_currRecDepth_1087_; lean_object* v_maxRecDepth_1088_; lean_object* v_ref_1089_; lean_object* v_currNamespace_1090_; lean_object* v_openDecls_1091_; lean_object* v_initHeartbeats_1092_; lean_object* v_maxHeartbeats_1093_; lean_object* v_quotContext_1094_; lean_object* v_currMacroScope_1095_; uint8_t v_diag_1096_; lean_object* v_cancelTk_x3f_1097_; uint8_t v_suppressElabErrors_1098_; lean_object* v_inheritedTraceOptions_1099_; lean_object* v_ref_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_fileName_1084_ = lean_ctor_get(v___y_1081_, 0);
v_fileMap_1085_ = lean_ctor_get(v___y_1081_, 1);
v_options_1086_ = lean_ctor_get(v___y_1081_, 2);
v_currRecDepth_1087_ = lean_ctor_get(v___y_1081_, 3);
v_maxRecDepth_1088_ = lean_ctor_get(v___y_1081_, 4);
v_ref_1089_ = lean_ctor_get(v___y_1081_, 5);
v_currNamespace_1090_ = lean_ctor_get(v___y_1081_, 6);
v_openDecls_1091_ = lean_ctor_get(v___y_1081_, 7);
v_initHeartbeats_1092_ = lean_ctor_get(v___y_1081_, 8);
v_maxHeartbeats_1093_ = lean_ctor_get(v___y_1081_, 9);
v_quotContext_1094_ = lean_ctor_get(v___y_1081_, 10);
v_currMacroScope_1095_ = lean_ctor_get(v___y_1081_, 11);
v_diag_1096_ = lean_ctor_get_uint8(v___y_1081_, sizeof(void*)*14);
v_cancelTk_x3f_1097_ = lean_ctor_get(v___y_1081_, 12);
v_suppressElabErrors_1098_ = lean_ctor_get_uint8(v___y_1081_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1099_ = lean_ctor_get(v___y_1081_, 13);
v_ref_1100_ = l_Lean_replaceRef(v_ref_1077_, v_ref_1089_);
lean_inc_ref(v_inheritedTraceOptions_1099_);
lean_inc(v_cancelTk_x3f_1097_);
lean_inc(v_currMacroScope_1095_);
lean_inc(v_quotContext_1094_);
lean_inc(v_maxHeartbeats_1093_);
lean_inc(v_initHeartbeats_1092_);
lean_inc(v_openDecls_1091_);
lean_inc(v_currNamespace_1090_);
lean_inc(v_maxRecDepth_1088_);
lean_inc(v_currRecDepth_1087_);
lean_inc_ref(v_options_1086_);
lean_inc_ref(v_fileMap_1085_);
lean_inc_ref(v_fileName_1084_);
v___x_1101_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1101_, 0, v_fileName_1084_);
lean_ctor_set(v___x_1101_, 1, v_fileMap_1085_);
lean_ctor_set(v___x_1101_, 2, v_options_1086_);
lean_ctor_set(v___x_1101_, 3, v_currRecDepth_1087_);
lean_ctor_set(v___x_1101_, 4, v_maxRecDepth_1088_);
lean_ctor_set(v___x_1101_, 5, v_ref_1100_);
lean_ctor_set(v___x_1101_, 6, v_currNamespace_1090_);
lean_ctor_set(v___x_1101_, 7, v_openDecls_1091_);
lean_ctor_set(v___x_1101_, 8, v_initHeartbeats_1092_);
lean_ctor_set(v___x_1101_, 9, v_maxHeartbeats_1093_);
lean_ctor_set(v___x_1101_, 10, v_quotContext_1094_);
lean_ctor_set(v___x_1101_, 11, v_currMacroScope_1095_);
lean_ctor_set(v___x_1101_, 12, v_cancelTk_x3f_1097_);
lean_ctor_set(v___x_1101_, 13, v_inheritedTraceOptions_1099_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*14, v_diag_1096_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*14 + 1, v_suppressElabErrors_1098_);
v___x_1102_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v_msg_1078_, v___y_1079_, v___y_1080_, v___x_1101_, v___y_1082_);
lean_dec_ref(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_ref_1103_, lean_object* v_msg_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(v_ref_1103_, v_msg_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v_ref_1103_);
return v_res_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
lean_ctor_set(v___x_1116_, 3, v___x_1115_);
lean_ctor_set(v___x_1116_, 4, v___x_1114_);
lean_ctor_set(v___x_1116_, 5, v___x_1114_);
lean_ctor_set(v___x_1116_, 6, v___x_1114_);
lean_ctor_set(v___x_1116_, 7, v___x_1114_);
lean_ctor_set(v___x_1116_, 8, v___x_1114_);
lean_ctor_set(v___x_1116_, 9, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_unsigned_to_nat(32u);
v___x_1118_ = lean_mk_empty_array_with_capacity(v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1120_ = ((size_t)5ULL);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_unsigned_to_nat(32u);
v___x_1123_ = lean_mk_empty_array_with_capacity(v___x_1122_);
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3);
v___x_1125_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v___x_1123_);
lean_ctor_set(v___x_1125_, 2, v___x_1121_);
lean_ctor_set(v___x_1125_, 3, v___x_1121_);
lean_ctor_set_usize(v___x_1125_, 4, v___x_1120_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_box(1);
v___x_1127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1);
v___x_1129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1127_);
lean_ctor_set(v___x_1129_, 2, v___x_1126_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(lean_object* v_msg_1151_, lean_object* v_declHint_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v_env_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_st_ref_get(v___y_1153_);
v_env_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_env_1156_);
lean_dec(v___x_1155_);
v___x_1157_ = l_Lean_Name_isAnonymous(v_declHint_1152_);
if (v___x_1157_ == 0)
{
uint8_t v_isExporting_1158_; 
v_isExporting_1158_ = lean_ctor_get_uint8(v_env_1156_, sizeof(void*)*8);
if (v_isExporting_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_env_1156_);
lean_dec(v_declHint_1152_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_msg_1151_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
lean_inc_ref(v_env_1156_);
v___x_1160_ = l_Lean_Environment_setExporting(v_env_1156_, v___x_1157_);
lean_inc(v_declHint_1152_);
lean_inc_ref(v___x_1160_);
v___x_1161_ = l_Lean_Environment_contains(v___x_1160_, v_declHint_1152_, v_isExporting_1158_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_dec_ref(v___x_1160_);
lean_dec_ref(v_env_1156_);
lean_dec(v_declHint_1152_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_msg_1151_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_c_1168_; lean_object* v___x_1169_; 
v___x_1163_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2);
v___x_1164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5);
v___x_1165_ = l_Lean_Options_empty;
v___x_1166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1160_);
lean_ctor_set(v___x_1166_, 1, v___x_1163_);
lean_ctor_set(v___x_1166_, 2, v___x_1164_);
lean_ctor_set(v___x_1166_, 3, v___x_1165_);
lean_inc(v_declHint_1152_);
v___x_1167_ = l_Lean_MessageData_ofConstName(v_declHint_1152_, v___x_1157_);
v_c_1168_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1168_, 0, v___x_1166_);
lean_ctor_set(v_c_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1156_, v_declHint_1152_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v_env_1156_);
lean_dec(v_declHint_1152_);
v___x_1170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v_c_1168_);
v___x_1172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = l_Lean_MessageData_note(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_msg_1151_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1212_; 
v_val_1177_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1179_ = v___x_1169_;
v_isShared_1180_ = v_isSharedCheck_1212_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_val_1177_);
lean_dec(v___x_1169_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1212_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_mod_1184_; uint8_t v___x_1185_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_Environment_header(v_env_1156_);
lean_dec_ref(v_env_1156_);
v___x_1183_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1182_);
v_mod_1184_ = lean_array_get(v___x_1181_, v___x_1183_, v_val_1177_);
lean_dec(v_val_1177_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = l_Lean_isPrivateName(v_declHint_1152_);
lean_dec(v_declHint_1152_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_c_1168_);
v___x_1188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_MessageData_ofName(v_mod_1184_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_MessageData_note(v___x_1193_);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_msg_1151_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1195_);
v___x_1197_ = v___x_1179_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_c_1168_);
v___x_1201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_Lean_MessageData_ofName(v_mod_1184_);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_MessageData_note(v___x_1206_);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_msg_1151_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1208_);
v___x_1210_ = v___x_1179_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1213_; 
lean_dec_ref(v_env_1156_);
lean_dec(v_declHint_1152_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_msg_1151_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___boxed(lean_object* v_msg_1214_, lean_object* v_declHint_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(v_msg_1214_, v_declHint_1215_, v___y_1216_);
lean_dec(v___y_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(lean_object* v_msg_1219_, lean_object* v_declHint_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1236_; 
v___x_1226_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(v_msg_1219_, v_declHint_1220_, v___y_1224_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1236_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1236_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1231_ = l_Lean_unknownIdentifierMessageTag;
v___x_1232_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_a_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16___boxed(lean_object* v_msg_1237_, lean_object* v_declHint_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(v_msg_1237_, v_declHint_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(lean_object* v_ref_1245_, lean_object* v_msg_1246_, lean_object* v_declHint_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; 
v___x_1253_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(v_msg_1246_, v_declHint_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(v_ref_1245_, v_a_1254_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg___boxed(lean_object* v_ref_1256_, lean_object* v_msg_1257_, lean_object* v_declHint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(v_ref_1256_, v_msg_1257_, v_declHint_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_ref_1256_);
return v_res_1264_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_ref_1271_, lean_object* v_constName_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1278_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1);
v___x_1279_ = 0;
lean_inc(v_constName_1272_);
v___x_1280_ = l_Lean_MessageData_ofConstName(v_constName_1272_, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1278_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(v_ref_1271_, v___x_1283_, v_constName_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_ref_1285_, lean_object* v_constName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_1285_, v_constName_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v_ref_1285_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_ref_1299_; lean_object* v___x_1300_; 
v_ref_1299_ = lean_ctor_get(v___y_1296_, 5);
v___x_1300_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_1299_, v_constName_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_constName_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(lean_object* v_constName_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v_env_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = lean_st_ref_get(v___y_1312_);
v_env_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_ref(v_env_1315_);
lean_dec(v___x_1314_);
v___x_1316_ = 0;
lean_inc(v_constName_1308_);
v___x_1317_ = l_Lean_Environment_findConstVal_x3f(v_env_1315_, v_constName_1308_, v___x_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1318_;
}
else
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_constName_1308_);
v_val_1319_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1317_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v___x_1317_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 0);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_val_1319_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3___boxed(lean_object* v_constName_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object* v_constName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
lean_inc(v_constName_1334_);
v___x_1340_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1352_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_levelParams_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v_levelParams_1345_ = lean_ctor_get(v_a_1341_, 1);
lean_inc(v_levelParams_1345_);
lean_dec(v_a_1341_);
v___x_1346_ = lean_box(0);
v___x_1347_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(v_levelParams_1345_, v___x_1346_);
v___x_1348_ = l_Lean_mkConst(v_constName_1334_, v___x_1347_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1348_);
v___x_1350_ = v___x_1343_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_constName_1334_);
v_a_1353_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1340_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1340_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object* v_constName_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_constName_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(lean_object* v_as_1368_, size_t v_i_1369_, size_t v_stop_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_eq(v_i_1369_, v_stop_1370_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_array_uget_borrowed(v_as_1368_, v_i_1369_);
lean_inc(v___x_1378_);
v___x_1379_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v___x_1378_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_n(v_a_1380_, 2);
lean_dec_ref(v___x_1379_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
v___x_1381_ = lean_infer_type(v_a_1380_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = l_Lean_Meta_isClass_x3f(v_a_1382_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_a_1386_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v___x_1390_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3));
v___x_1391_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_a_1384_, v___x_1390_);
lean_dec(v_a_1384_);
if (v___x_1391_ == 0)
{
lean_dec(v_a_1380_);
v_a_1386_ = v_b_1371_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1392_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
v___x_1393_ = l_Lean_MessageData_ofConst(v_a_1380_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1392_);
v___x_1396_ = lean_array_push(v_b_1371_, v___x_1395_);
v_a_1386_ = v___x_1396_;
goto v___jp_1385_;
}
v___jp_1385_:
{
size_t v___x_1387_; size_t v___x_1388_; 
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_add(v_i_1369_, v___x_1387_);
v_i_1369_ = v___x_1388_;
v_b_1371_ = v_a_1386_;
goto _start;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_a_1380_);
lean_dec_ref(v_b_1371_);
v_a_1397_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1383_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1383_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_a_1380_);
lean_dec_ref(v_b_1371_);
v_a_1405_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1381_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1381_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_b_1371_);
v_a_1413_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1379_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1379_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_b_1371_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8___boxed(lean_object* v_as_1422_, lean_object* v_i_1423_, lean_object* v_stop_1424_, lean_object* v_b_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
size_t v_i_boxed_1431_; size_t v_stop_boxed_1432_; lean_object* v_res_1433_; 
v_i_boxed_1431_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_stop_boxed_1432_ = lean_unbox_usize(v_stop_1424_);
lean_dec(v_stop_1424_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_1422_, v_i_boxed_1431_, v_stop_boxed_1432_, v_b_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v_as_1422_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(lean_object* v_as_1436_, lean_object* v_start_1437_, lean_object* v_stop_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0));
v___x_1445_ = lean_nat_dec_lt(v_start_1437_, v_stop_1438_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_array_get_size(v_as_1436_);
v___x_1448_ = lean_nat_dec_le(v_stop_1438_, v___x_1447_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_nat_dec_lt(v_start_1437_, v___x_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1444_);
return v___x_1450_;
}
else
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_usize_of_nat(v_start_1437_);
v___x_1452_ = lean_usize_of_nat(v___x_1447_);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_1436_, v___x_1451_, v___x_1452_, v___x_1444_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1453_;
}
}
else
{
size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_usize_of_nat(v_start_1437_);
v___x_1455_ = lean_usize_of_nat(v_stop_1438_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_1436_, v___x_1454_, v___x_1455_, v___x_1444_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(lean_object* v_as_1457_, lean_object* v_start_1458_, lean_object* v_stop_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v_as_1457_, v_start_1458_, v_stop_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_stop_1459_);
lean_dec(v_start_1458_);
lean_dec_ref(v_as_1457_);
return v_res_1465_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2);
v___x_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
lean_ctor_set(v___x_1472_, 2, v___x_1471_);
lean_ctor_set(v___x_1472_, 3, v___x_1471_);
lean_ctor_set(v___x_1472_, 4, v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(lean_object* v_s_1478_, lean_object* v___f_1479_, uint8_t v___x_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1532_; lean_object* v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___x_1607_; lean_object* v_fileName_1608_; lean_object* v_fileMap_1609_; lean_object* v_options_1610_; lean_object* v_currRecDepth_1611_; lean_object* v_ref_1612_; lean_object* v_currNamespace_1613_; lean_object* v_openDecls_1614_; lean_object* v_initHeartbeats_1615_; lean_object* v_maxHeartbeats_1616_; lean_object* v_quotContext_1617_; lean_object* v_currMacroScope_1618_; lean_object* v_cancelTk_x3f_1619_; uint8_t v_suppressElabErrors_1620_; lean_object* v_inheritedTraceOptions_1621_; lean_object* v_env_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v_fileName_1627_; lean_object* v_fileMap_1628_; lean_object* v_currRecDepth_1629_; lean_object* v_ref_1630_; lean_object* v_currNamespace_1631_; lean_object* v_openDecls_1632_; lean_object* v_initHeartbeats_1633_; lean_object* v_maxHeartbeats_1634_; lean_object* v_quotContext_1635_; lean_object* v_currMacroScope_1636_; lean_object* v_cancelTk_x3f_1637_; uint8_t v_suppressElabErrors_1638_; lean_object* v_inheritedTraceOptions_1639_; lean_object* v___y_1640_; uint8_t v___y_1671_; uint8_t v___x_1692_; 
v___x_1607_ = lean_st_ref_get(v___y_1484_);
v_fileName_1608_ = lean_ctor_get(v___y_1483_, 0);
v_fileMap_1609_ = lean_ctor_get(v___y_1483_, 1);
v_options_1610_ = lean_ctor_get(v___y_1483_, 2);
v_currRecDepth_1611_ = lean_ctor_get(v___y_1483_, 3);
v_ref_1612_ = lean_ctor_get(v___y_1483_, 5);
v_currNamespace_1613_ = lean_ctor_get(v___y_1483_, 6);
v_openDecls_1614_ = lean_ctor_get(v___y_1483_, 7);
v_initHeartbeats_1615_ = lean_ctor_get(v___y_1483_, 8);
v_maxHeartbeats_1616_ = lean_ctor_get(v___y_1483_, 9);
v_quotContext_1617_ = lean_ctor_get(v___y_1483_, 10);
v_currMacroScope_1618_ = lean_ctor_get(v___y_1483_, 11);
v_cancelTk_x3f_1619_ = lean_ctor_get(v___y_1483_, 12);
v_suppressElabErrors_1620_ = lean_ctor_get_uint8(v___y_1483_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1621_ = lean_ctor_get(v___y_1483_, 13);
v_env_1622_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1622_);
lean_dec(v___x_1607_);
v___x_1623_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1610_);
v___x_1624_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_1610_, v___x_1623_, v___x_1480_);
v___x_1625_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_1624_, v___x_1623_);
v___x_1692_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1622_);
lean_dec_ref(v_env_1622_);
if (v___x_1692_ == 0)
{
if (v___x_1625_ == 0)
{
v_fileName_1627_ = v_fileName_1608_;
v_fileMap_1628_ = v_fileMap_1609_;
v_currRecDepth_1629_ = v_currRecDepth_1611_;
v_ref_1630_ = v_ref_1612_;
v_currNamespace_1631_ = v_currNamespace_1613_;
v_openDecls_1632_ = v_openDecls_1614_;
v_initHeartbeats_1633_ = v_initHeartbeats_1615_;
v_maxHeartbeats_1634_ = v_maxHeartbeats_1616_;
v_quotContext_1635_ = v_quotContext_1617_;
v_currMacroScope_1636_ = v_currMacroScope_1618_;
v_cancelTk_x3f_1637_ = v_cancelTk_x3f_1619_;
v_suppressElabErrors_1638_ = v_suppressElabErrors_1620_;
v_inheritedTraceOptions_1639_ = v_inheritedTraceOptions_1621_;
v___y_1640_ = v___y_1484_;
goto v___jp_1626_;
}
else
{
v___y_1671_ = v___x_1692_;
goto v___jp_1670_;
}
}
else
{
v___y_1671_ = v___x_1625_;
goto v___jp_1670_;
}
v___jp_1486_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_array_get_size(v___y_1491_);
v___x_1493_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v___y_1491_, v___y_1490_, v___x_1492_, v___y_1481_, v___y_1482_, v___y_1488_, v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1491_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___y_1487_);
lean_ctor_set(v___x_1498_, 1, v_a_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v___y_1487_);
v_a_1503_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1493_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1493_);
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
v___jp_1511_:
{
lean_object* v___x_1520_; 
v___x_1520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v___y_1518_, v___y_1516_, v___y_1515_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
v___y_1487_ = v___y_1512_;
v___y_1488_ = v___y_1513_;
v___y_1489_ = v___y_1514_;
v___y_1490_ = v___y_1517_;
v___y_1491_ = v___x_1520_;
goto v___jp_1486_;
}
v___jp_1521_:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_nat_dec_le(v___y_1529_, v___y_1525_);
if (v___x_1530_ == 0)
{
lean_dec(v___y_1525_);
lean_inc(v___y_1529_);
v___y_1512_ = v___y_1522_;
v___y_1513_ = v___y_1523_;
v___y_1514_ = v___y_1524_;
v___y_1515_ = v___y_1529_;
v___y_1516_ = v___y_1526_;
v___y_1517_ = v___y_1527_;
v___y_1518_ = v___y_1528_;
v___y_1519_ = v___y_1529_;
goto v___jp_1511_;
}
else
{
v___y_1512_ = v___y_1522_;
v___y_1513_ = v___y_1523_;
v___y_1514_ = v___y_1524_;
v___y_1515_ = v___y_1529_;
v___y_1516_ = v___y_1526_;
v___y_1517_ = v___y_1527_;
v___y_1518_ = v___y_1528_;
v___y_1519_ = v___y_1525_;
goto v___jp_1511_;
}
}
v___jp_1531_:
{
lean_object* v___x_1535_; uint8_t v_foApprox_1536_; uint8_t v_ctxApprox_1537_; uint8_t v_quasiPatternApprox_1538_; uint8_t v_constApprox_1539_; uint8_t v_isDefEqStuckEx_1540_; uint8_t v_unificationHints_1541_; uint8_t v_proofIrrelevance_1542_; uint8_t v_assignSyntheticOpaque_1543_; uint8_t v_offsetCnstrs_1544_; uint8_t v_etaStruct_1545_; uint8_t v_univApprox_1546_; uint8_t v_iota_1547_; uint8_t v_beta_1548_; uint8_t v_proj_1549_; uint8_t v_zeta_1550_; uint8_t v_zetaDelta_1551_; uint8_t v_zetaUnused_1552_; uint8_t v_zetaHave_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1599_; 
v___x_1535_ = l_Lean_Meta_Context_config(v___y_1481_);
v_foApprox_1536_ = lean_ctor_get_uint8(v___x_1535_, 0);
v_ctxApprox_1537_ = lean_ctor_get_uint8(v___x_1535_, 1);
v_quasiPatternApprox_1538_ = lean_ctor_get_uint8(v___x_1535_, 2);
v_constApprox_1539_ = lean_ctor_get_uint8(v___x_1535_, 3);
v_isDefEqStuckEx_1540_ = lean_ctor_get_uint8(v___x_1535_, 4);
v_unificationHints_1541_ = lean_ctor_get_uint8(v___x_1535_, 5);
v_proofIrrelevance_1542_ = lean_ctor_get_uint8(v___x_1535_, 6);
v_assignSyntheticOpaque_1543_ = lean_ctor_get_uint8(v___x_1535_, 7);
v_offsetCnstrs_1544_ = lean_ctor_get_uint8(v___x_1535_, 8);
v_etaStruct_1545_ = lean_ctor_get_uint8(v___x_1535_, 10);
v_univApprox_1546_ = lean_ctor_get_uint8(v___x_1535_, 11);
v_iota_1547_ = lean_ctor_get_uint8(v___x_1535_, 12);
v_beta_1548_ = lean_ctor_get_uint8(v___x_1535_, 13);
v_proj_1549_ = lean_ctor_get_uint8(v___x_1535_, 14);
v_zeta_1550_ = lean_ctor_get_uint8(v___x_1535_, 15);
v_zetaDelta_1551_ = lean_ctor_get_uint8(v___x_1535_, 16);
v_zetaUnused_1552_ = lean_ctor_get_uint8(v___x_1535_, 17);
v_zetaHave_1553_ = lean_ctor_get_uint8(v___x_1535_, 18);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1555_ = v___x_1535_;
v_isShared_1556_ = v_isSharedCheck_1599_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1535_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1599_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
uint8_t v_trackZetaDelta_1557_; lean_object* v_zetaDeltaSet_1558_; lean_object* v_lctx_1559_; lean_object* v_localInstances_1560_; lean_object* v_defEqCtx_x3f_1561_; lean_object* v_synthPendingDepth_1562_; lean_object* v_canUnfold_x3f_1563_; uint8_t v_univApprox_1564_; uint8_t v_inTypeClassResolution_1565_; uint8_t v_cacheInferType_1566_; lean_object* v_config_1568_; 
v_trackZetaDelta_1557_ = lean_ctor_get_uint8(v___y_1481_, sizeof(void*)*7);
v_zetaDeltaSet_1558_ = lean_ctor_get(v___y_1481_, 1);
v_lctx_1559_ = lean_ctor_get(v___y_1481_, 2);
v_localInstances_1560_ = lean_ctor_get(v___y_1481_, 3);
v_defEqCtx_x3f_1561_ = lean_ctor_get(v___y_1481_, 4);
v_synthPendingDepth_1562_ = lean_ctor_get(v___y_1481_, 5);
v_canUnfold_x3f_1563_ = lean_ctor_get(v___y_1481_, 6);
v_univApprox_1564_ = lean_ctor_get_uint8(v___y_1481_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1565_ = lean_ctor_get_uint8(v___y_1481_, sizeof(void*)*7 + 2);
v_cacheInferType_1566_ = lean_ctor_get_uint8(v___y_1481_, sizeof(void*)*7 + 3);
if (v_isShared_1556_ == 0)
{
v_config_1568_ = v___x_1555_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 0, v_foApprox_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 1, v_ctxApprox_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 2, v_quasiPatternApprox_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 3, v_constApprox_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 4, v_isDefEqStuckEx_1540_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 5, v_unificationHints_1541_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 6, v_proofIrrelevance_1542_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 7, v_assignSyntheticOpaque_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 8, v_offsetCnstrs_1544_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 10, v_etaStruct_1545_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 11, v_univApprox_1546_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 12, v_iota_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 13, v_beta_1548_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 14, v_proj_1549_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 15, v_zeta_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 16, v_zetaDelta_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 17, v_zetaUnused_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, 18, v_zetaHave_1553_);
v_config_1568_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
uint64_t v___x_1569_; uint64_t v___x_1570_; uint64_t v___x_1571_; uint64_t v___x_1572_; uint64_t v___x_1573_; uint64_t v_key_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_ctor_set_uint8(v_config_1568_, 9, v___y_1534_);
v___x_1569_ = l_Lean_Meta_Context_configKey(v___y_1481_);
v___x_1570_ = 2ULL;
v___x_1571_ = lean_uint64_shift_right(v___x_1569_, v___x_1570_);
v___x_1572_ = lean_uint64_shift_left(v___x_1571_, v___x_1570_);
v___x_1573_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1534_);
v_key_1574_ = lean_uint64_lor(v___x_1572_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1575_, 0, v_config_1568_);
lean_ctor_set_uint64(v___x_1575_, sizeof(void*)*1, v_key_1574_);
lean_inc(v_canUnfold_x3f_1563_);
lean_inc(v_synthPendingDepth_1562_);
lean_inc(v_defEqCtx_x3f_1561_);
lean_inc_ref(v_localInstances_1560_);
lean_inc_ref(v_lctx_1559_);
lean_inc(v_zetaDeltaSet_1558_);
v___x_1576_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v_zetaDeltaSet_1558_);
lean_ctor_set(v___x_1576_, 2, v_lctx_1559_);
lean_ctor_set(v___x_1576_, 3, v_localInstances_1560_);
lean_ctor_set(v___x_1576_, 4, v_defEqCtx_x3f_1561_);
lean_ctor_set(v___x_1576_, 5, v_synthPendingDepth_1562_);
lean_ctor_set(v___x_1576_, 6, v_canUnfold_x3f_1563_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7, v_trackZetaDelta_1557_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7 + 1, v_univApprox_1564_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1565_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*7 + 3, v_cacheInferType_1566_);
lean_inc_ref(v___y_1532_);
v___x_1577_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_1478_, v___x_1576_, v___y_1482_, v___y_1532_, v___y_1533_);
lean_dec_ref(v___x_1576_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v_diag_1580_; lean_object* v_unfoldCounter_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = lean_st_ref_get(v___y_1482_);
v_diag_1580_ = lean_ctor_get(v___x_1579_, 4);
lean_inc_ref(v_diag_1580_);
lean_dec(v___x_1579_);
v_unfoldCounter_1581_ = lean_ctor_get(v_diag_1580_, 0);
lean_inc_ref(v_unfoldCounter_1581_);
lean_dec_ref(v_diag_1580_);
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_1584_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_unfoldCounter_1581_, v___f_1479_, v___x_1583_);
lean_dec_ref(v_unfoldCounter_1581_);
v___x_1585_ = lean_array_get_size(v___x_1584_);
v___x_1586_ = lean_nat_dec_eq(v___x_1585_, v___x_1582_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_nat_sub(v___x_1585_, v___x_1587_);
v___x_1589_ = lean_nat_dec_le(v___x_1582_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_inc(v___x_1588_);
v___y_1522_ = v_a_1578_;
v___y_1523_ = v___y_1532_;
v___y_1524_ = v___y_1533_;
v___y_1525_ = v___x_1588_;
v___y_1526_ = v___x_1584_;
v___y_1527_ = v___x_1582_;
v___y_1528_ = v___x_1585_;
v___y_1529_ = v___x_1588_;
goto v___jp_1521_;
}
else
{
v___y_1522_ = v_a_1578_;
v___y_1523_ = v___y_1532_;
v___y_1524_ = v___y_1533_;
v___y_1525_ = v___x_1588_;
v___y_1526_ = v___x_1584_;
v___y_1527_ = v___x_1582_;
v___y_1528_ = v___x_1585_;
v___y_1529_ = v___x_1582_;
goto v___jp_1521_;
}
}
else
{
v___y_1487_ = v_a_1578_;
v___y_1488_ = v___y_1532_;
v___y_1489_ = v___y_1533_;
v___y_1490_ = v___x_1582_;
v___y_1491_ = v___x_1584_;
goto v___jp_1486_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v___y_1532_);
lean_dec_ref(v___f_1479_);
v_a_1590_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1577_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1577_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
v___jp_1600_:
{
lean_object* v___x_1603_; uint8_t v_transparency_1604_; uint8_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1603_ = l_Lean_Meta_Context_config(v___y_1481_);
v_transparency_1604_ = lean_ctor_get_uint8(v___x_1603_, 9);
lean_dec_ref(v___x_1603_);
v___x_1605_ = 1;
v___x_1606_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
v___y_1532_ = v___y_1601_;
v___y_1533_ = v___y_1602_;
v___y_1534_ = v_transparency_1604_;
goto v___jp_1531_;
}
else
{
v___y_1532_ = v___y_1601_;
v___y_1533_ = v___y_1602_;
v___y_1534_ = v___x_1605_;
goto v___jp_1531_;
}
}
v___jp_1626_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1641_ = l_Lean_maxRecDepth;
v___x_1642_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_1624_, v___x_1641_);
lean_inc_ref(v_inheritedTraceOptions_1639_);
lean_inc(v_cancelTk_x3f_1637_);
lean_inc(v_currMacroScope_1636_);
lean_inc(v_quotContext_1635_);
lean_inc(v_maxHeartbeats_1634_);
lean_inc(v_initHeartbeats_1633_);
lean_inc(v_openDecls_1632_);
lean_inc(v_currNamespace_1631_);
lean_inc(v_ref_1630_);
lean_inc(v_currRecDepth_1629_);
lean_inc_ref(v_fileMap_1628_);
lean_inc_ref(v_fileName_1627_);
v___x_1643_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1643_, 0, v_fileName_1627_);
lean_ctor_set(v___x_1643_, 1, v_fileMap_1628_);
lean_ctor_set(v___x_1643_, 2, v___x_1624_);
lean_ctor_set(v___x_1643_, 3, v_currRecDepth_1629_);
lean_ctor_set(v___x_1643_, 4, v___x_1642_);
lean_ctor_set(v___x_1643_, 5, v_ref_1630_);
lean_ctor_set(v___x_1643_, 6, v_currNamespace_1631_);
lean_ctor_set(v___x_1643_, 7, v_openDecls_1632_);
lean_ctor_set(v___x_1643_, 8, v_initHeartbeats_1633_);
lean_ctor_set(v___x_1643_, 9, v_maxHeartbeats_1634_);
lean_ctor_set(v___x_1643_, 10, v_quotContext_1635_);
lean_ctor_set(v___x_1643_, 11, v_currMacroScope_1636_);
lean_ctor_set(v___x_1643_, 12, v_cancelTk_x3f_1637_);
lean_ctor_set(v___x_1643_, 13, v_inheritedTraceOptions_1639_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*14, v___x_1625_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*14 + 1, v_suppressElabErrors_1638_);
v___x_1644_ = l_Lean_isDiagnosticsEnabled___redArg(v___x_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; uint8_t v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1644_);
v___x_1646_ = lean_unbox(v_a_1645_);
lean_dec(v_a_1645_);
if (v___x_1646_ == 0)
{
v___y_1601_ = v___x_1643_;
v___y_1602_ = v___y_1640_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1647_; lean_object* v_mctx_1648_; lean_object* v_cache_1649_; lean_object* v_zetaDeltaFVarIds_1650_; lean_object* v_postponed_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v___x_1647_ = lean_st_ref_take(v___y_1482_);
v_mctx_1648_ = lean_ctor_get(v___x_1647_, 0);
v_cache_1649_ = lean_ctor_get(v___x_1647_, 1);
v_zetaDeltaFVarIds_1650_ = lean_ctor_get(v___x_1647_, 2);
v_postponed_1651_ = lean_ctor_get(v___x_1647_, 3);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v___x_1647_, 4);
lean_dec(v_unused_1661_);
v___x_1653_ = v___x_1647_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_postponed_1651_);
lean_inc(v_zetaDeltaFVarIds_1650_);
lean_inc(v_cache_1649_);
lean_inc(v_mctx_1648_);
lean_dec(v___x_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_mctx_1648_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_cache_1649_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_zetaDeltaFVarIds_1650_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v_postponed_1651_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_st_ref_set(v___y_1482_, v___x_1657_);
v___y_1601_ = v___x_1643_;
v___y_1602_ = v___y_1640_;
goto v___jp_1600_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v___x_1643_);
lean_dec_ref(v___f_1479_);
lean_dec_ref(v_s_1478_);
v_a_1662_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1644_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1644_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
v___jp_1670_:
{
if (v___y_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v_env_1673_; lean_object* v_nextMacroScope_1674_; lean_object* v_ngen_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_traceState_1677_; lean_object* v_messages_1678_; lean_object* v_infoState_1679_; lean_object* v_snapshotTasks_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1690_; 
v___x_1672_ = lean_st_ref_take(v___y_1484_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
v_nextMacroScope_1674_ = lean_ctor_get(v___x_1672_, 1);
v_ngen_1675_ = lean_ctor_get(v___x_1672_, 2);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1672_, 3);
v_traceState_1677_ = lean_ctor_get(v___x_1672_, 4);
v_messages_1678_ = lean_ctor_get(v___x_1672_, 6);
v_infoState_1679_ = lean_ctor_get(v___x_1672_, 7);
v_snapshotTasks_1680_ = lean_ctor_get(v___x_1672_, 8);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1672_, 5);
lean_dec(v_unused_1691_);
v___x_1682_ = v___x_1672_;
v_isShared_1683_ = v_isSharedCheck_1690_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_snapshotTasks_1680_);
lean_inc(v_infoState_1679_);
lean_inc(v_messages_1678_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_ngen_1675_);
lean_inc(v_nextMacroScope_1674_);
lean_inc(v_env_1673_);
lean_dec(v___x_1672_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1690_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1684_ = l_Lean_Kernel_enableDiag(v_env_1673_, v___x_1625_);
v___x_1685_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 5, v___x_1685_);
lean_ctor_set(v___x_1682_, 0, v___x_1684_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_nextMacroScope_1674_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_ngen_1675_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_traceState_1677_);
lean_ctor_set(v_reuseFailAlloc_1689_, 5, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 6, v_messages_1678_);
lean_ctor_set(v_reuseFailAlloc_1689_, 7, v_infoState_1679_);
lean_ctor_set(v_reuseFailAlloc_1689_, 8, v_snapshotTasks_1680_);
v___x_1687_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_st_ref_set(v___y_1484_, v___x_1687_);
v_fileName_1627_ = v_fileName_1608_;
v_fileMap_1628_ = v_fileMap_1609_;
v_currRecDepth_1629_ = v_currRecDepth_1611_;
v_ref_1630_ = v_ref_1612_;
v_currNamespace_1631_ = v_currNamespace_1613_;
v_openDecls_1632_ = v_openDecls_1614_;
v_initHeartbeats_1633_ = v_initHeartbeats_1615_;
v_maxHeartbeats_1634_ = v_maxHeartbeats_1616_;
v_quotContext_1635_ = v_quotContext_1617_;
v_currMacroScope_1636_ = v_currMacroScope_1618_;
v_cancelTk_x3f_1637_ = v_cancelTk_x3f_1619_;
v_suppressElabErrors_1638_ = v_suppressElabErrors_1620_;
v_inheritedTraceOptions_1639_ = v_inheritedTraceOptions_1621_;
v___y_1640_ = v___y_1484_;
goto v___jp_1626_;
}
}
}
else
{
v_fileName_1627_ = v_fileName_1608_;
v_fileMap_1628_ = v_fileMap_1609_;
v_currRecDepth_1629_ = v_currRecDepth_1611_;
v_ref_1630_ = v_ref_1612_;
v_currNamespace_1631_ = v_currNamespace_1613_;
v_openDecls_1632_ = v_openDecls_1614_;
v_initHeartbeats_1633_ = v_initHeartbeats_1615_;
v_maxHeartbeats_1634_ = v_maxHeartbeats_1616_;
v_quotContext_1635_ = v_quotContext_1617_;
v_currMacroScope_1636_ = v_currMacroScope_1618_;
v_cancelTk_x3f_1637_ = v_cancelTk_x3f_1619_;
v_suppressElabErrors_1638_ = v_suppressElabErrors_1620_;
v_inheritedTraceOptions_1639_ = v_inheritedTraceOptions_1621_;
v___y_1640_ = v___y_1484_;
goto v___jp_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(lean_object* v_s_1693_, lean_object* v___f_1694_, lean_object* v___x_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v___x_13211__boxed_1701_; lean_object* v_res_1702_; 
v___x_13211__boxed_1701_ = lean_unbox(v___x_1695_);
v_res_1702_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(v_s_1693_, v___f_1694_, v___x_13211__boxed_1701_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9));
v___x_1718_ = l_Lean_stringToMessageData(v___x_1717_);
return v___x_1718_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11));
v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18));
v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20));
v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22));
v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
return v___x_1739_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24));
v___x_1742_ = l_Lean_stringToMessageData(v___x_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* v_tacticName_1782_, lean_object* v_expectedType_1783_, lean_object* v_s_1784_, lean_object* v_r_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7));
v___x_1792_ = l_Lean_Expr_isAppOf(v_r_1785_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___f_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v___f_1793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0));
v___x_1794_ = 1;
v___x_1795_ = lean_box(v___x_1794_);
lean_inc_ref(v_s_1784_);
v___f_1796_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1796_, 0, v_s_1784_);
lean_closure_set(v___f_1796_, 1, v___f_1793_);
lean_closure_set(v___f_1796_, 2, v___x_1795_);
v___x_1797_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v___f_1796_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1929_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1929_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1929_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1928_; 
v_fst_1837_ = lean_ctor_get(v_a_1798_, 0);
v_snd_1838_ = lean_ctor_get(v_a_1798_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1840_ = v_a_1798_;
v_isShared_1841_ = v_isSharedCheck_1928_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_snd_1838_);
lean_inc(v_fst_1837_);
lean_dec(v_a_1798_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1928_;
goto v_resetjp_1839_;
}
v___jp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1805_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1806_ = l_Lean_MessageData_ofName(v_tacticName_1782_);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_indentExpr(v_expectedType_1783_);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_1815_ = l_Lean_MessageData_ofConstName(v___x_1814_, v___x_1792_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1813_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_indentExpr(v_s_1784_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5));
v___x_1824_ = l_Lean_MessageData_ofConstName(v___x_1823_, v___x_1792_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1822_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_MessageData_ofConstName(v___x_1791_, v___x_1792_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___y_1803_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___y_1804_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1833_);
v___x_1835_ = v___x_1800_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
v_resetjp_1839_:
{
lean_object* v___y_1843_; lean_object* v___y_1895_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = lean_array_get_size(v_snd_1838_);
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_nat_dec_eq(v___x_1913_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_dec_eq(v___x_1913_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46));
v___y_1895_ = v___x_1918_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1919_; 
v___x_1919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47));
v___y_1895_ = v___x_1919_;
goto v___jp_1894_;
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_snd_1838_);
v___x_1920_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49);
v___x_1921_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_1922_ = l_Lean_MessageData_ofConstName(v___x_1921_, v___x_1792_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1920_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
lean_inc(v_fst_1837_);
v___x_1926_ = l_Lean_indentExpr(v_fst_1837_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___y_1843_ = v___x_1927_;
goto v___jp_1842_;
}
v___jp_1842_:
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14));
v___x_1845_ = l_Lean_Expr_isAppOf(v_fst_1837_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17));
v___x_1847_ = l_Lean_Expr_isAppOf(v_fst_1837_, v___x_1846_);
lean_dec(v_fst_1837_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_del_object(v___x_1840_);
v___x_1848_ = l_Lean_MessageData_nil;
v___y_1803_ = v___y_1843_;
v___y_1804_ = v___x_1848_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19);
v___x_1850_ = l_Lean_MessageData_ofConstName(v___x_1846_, v___x_1792_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 7);
lean_ctor_set(v___x_1840_, 1, v___x_1850_);
lean_ctor_set(v___x_1840_, 0, v___x_1849_);
v___x_1852_ = v___x_1840_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_1856_ = l_Lean_MessageData_ofConstName(v___x_1855_, v___x_1792_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
lean_inc(v_tacticName_1782_);
v___x_1860_ = l_Lean_MessageData_ofName(v_tacticName_1782_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27));
v___x_1865_ = l_Lean_MessageData_ofConstName(v___x_1864_, v___x_1792_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1863_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_MessageData_hint_x27(v___x_1868_);
v___y_1803_ = v___y_1843_;
v___y_1804_ = v___x_1869_;
goto v___jp_1802_;
}
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v_fst_1837_);
v___x_1871_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29);
v___x_1872_ = l_Lean_MessageData_ofConstName(v___x_1844_, v___x_1792_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 7);
lean_ctor_set(v___x_1840_, 1, v___x_1872_);
lean_ctor_set(v___x_1840_, 0, v___x_1871_);
v___x_1874_ = v___x_1840_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1875_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_1878_ = l_Lean_MessageData_ofConstName(v___x_1877_, v___x_1792_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1876_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35));
v___x_1883_ = l_Lean_MessageData_ofConstName(v___x_1882_, v___x_1792_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37));
v___x_1888_ = l_Lean_MessageData_ofConstName(v___x_1887_, v___x_1792_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1886_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_MessageData_hint_x27(v___x_1891_);
v___y_1803_ = v___y_1843_;
v___y_1804_ = v___x_1892_;
goto v___jp_1802_;
}
}
}
v___jp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41);
lean_inc_ref(v___y_1895_);
v___x_1897_ = l_Lean_stringToMessageData(v___y_1895_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_array_to_list(v_snd_1838_);
v___x_1902_ = l_Lean_MessageData_andList(v___x_1901_);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1900_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_1907_ = l_Lean_MessageData_ofConstName(v___x_1906_, v___x_1792_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1905_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
lean_inc(v_fst_1837_);
v___x_1911_ = l_Lean_indentExpr(v_fst_1837_);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___y_1843_ = v___x_1912_;
goto v___jp_1842_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_s_1784_);
lean_dec_ref(v_expectedType_1783_);
lean_dec(v_tacticName_1782_);
v_a_1930_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1797_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1797_);
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
lean_dec_ref(v_s_1784_);
v___x_1938_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_1939_ = l_Lean_MessageData_ofName(v_tacticName_1782_);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_indentExpr(v_expectedType_1783_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(lean_object* v_00_u03c3_1958_, lean_object* v_00_u03b2_1959_, lean_object* v_map_1960_, lean_object* v_f_1961_, lean_object* v_init_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_1960_, v_f_1961_, v_init_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(lean_object* v_00_u03c3_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_map_1966_, lean_object* v_f_1967_, lean_object* v_init_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_00_u03c3_1964_, v_00_u03b2_1965_, v_map_1966_, v_f_1967_, v_init_1968_);
lean_dec_ref(v_map_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(lean_object* v_n_1970_, lean_object* v_as_1971_, lean_object* v_lo_1972_, lean_object* v_hi_1973_, lean_object* v_w_1974_, lean_object* v_hlo_1975_, lean_object* v_hhi_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_1970_, v_as_1971_, v_lo_1972_, v_hi_1973_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(lean_object* v_n_1978_, lean_object* v_as_1979_, lean_object* v_lo_1980_, lean_object* v_hi_1981_, lean_object* v_w_1982_, lean_object* v_hlo_1983_, lean_object* v_hhi_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v_n_1978_, v_as_1979_, v_lo_1980_, v_hi_1981_, v_w_1982_, v_hlo_1983_, v_hhi_1984_);
lean_dec(v_hi_1981_);
lean_dec(v_n_1978_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(lean_object* v_map_1986_, lean_object* v_f_1987_, lean_object* v_init_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_1987_, v_map_1986_, v_init_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg___boxed(lean_object* v_map_1990_, lean_object* v_f_1991_, lean_object* v_init_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(v_map_1990_, v_f_1991_, v_init_1992_);
lean_dec_ref(v_map_1990_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(lean_object* v_00_u03c3_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_map_1996_, lean_object* v_f_1997_, lean_object* v_init_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_1997_, v_map_1996_, v_init_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___boxed(lean_object* v_00_u03c3_2000_, lean_object* v_00_u03b2_2001_, lean_object* v_map_2002_, lean_object* v_f_2003_, lean_object* v_init_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(v_00_u03c3_2000_, v_00_u03b2_2001_, v_map_2002_, v_f_2003_, v_init_2004_);
lean_dec_ref(v_map_2002_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10(lean_object* v_n_2006_, lean_object* v_lo_2007_, lean_object* v_hi_2008_, lean_object* v_hhi_2009_, lean_object* v_pivot_2010_, lean_object* v_as_2011_, lean_object* v_i_2012_, lean_object* v_k_2013_, lean_object* v_ilo_2014_, lean_object* v_ik_2015_, lean_object* v_w_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(v_hi_2008_, v_pivot_2010_, v_as_2011_, v_i_2012_, v_k_2013_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___boxed(lean_object* v_n_2018_, lean_object* v_lo_2019_, lean_object* v_hi_2020_, lean_object* v_hhi_2021_, lean_object* v_pivot_2022_, lean_object* v_as_2023_, lean_object* v_i_2024_, lean_object* v_k_2025_, lean_object* v_ilo_2026_, lean_object* v_ik_2027_, lean_object* v_w_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10(v_n_2018_, v_lo_2019_, v_hi_2020_, v_hhi_2021_, v_pivot_2022_, v_as_2023_, v_i_2024_, v_k_2025_, v_ilo_2026_, v_ik_2027_, v_w_2028_);
lean_dec(v_pivot_2022_);
lean_dec(v_hi_2020_);
lean_dec(v_lo_2019_);
lean_dec(v_n_2018_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_2030_, lean_object* v_constName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_constName_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(v_00_u03b1_2038_, v_constName_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(lean_object* v_00_u03c3_2046_, lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_f_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_2049_, v_x_2050_, v_x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03c3_2053_, lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_f_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(v_00_u03c3_2053_, v_00_u03b1_2054_, v_00_u03b2_2055_, v_f_2056_, v_x_2057_, v_x_2058_);
lean_dec_ref(v_x_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b1_2060_, lean_object* v_ref_2061_, lean_object* v_constName_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_2061_, v_constName_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_ref_2070_, lean_object* v_constName_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(v_00_u03b1_2069_, v_ref_2070_, v_constName_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v_ref_2070_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_00_u03c3_2080_, lean_object* v_f_2081_, lean_object* v_as_2082_, size_t v_i_2083_, size_t v_stop_2084_, lean_object* v_b_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_2081_, v_as_2082_, v_i_2083_, v_stop_2084_, v_b_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_00_u03c3_2089_, lean_object* v_f_2090_, lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_){
_start:
{
size_t v_i_boxed_2095_; size_t v_stop_boxed_2096_; lean_object* v_res_2097_; 
v_i_boxed_2095_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2096_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(v_00_u03b1_2087_, v_00_u03b2_2088_, v_00_u03c3_2089_, v_f_2090_, v_as_2091_, v_i_boxed_2095_, v_stop_boxed_2096_, v_b_2094_);
lean_dec_ref(v_as_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(lean_object* v_00_u03c3_2098_, lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_f_2101_, lean_object* v_keys_2102_, lean_object* v_vals_2103_, lean_object* v_heq_2104_, lean_object* v_i_2105_, lean_object* v_acc_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_2101_, v_keys_2102_, v_vals_2103_, v_i_2105_, v_acc_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___boxed(lean_object* v_00_u03c3_2108_, lean_object* v_00_u03b1_2109_, lean_object* v_00_u03b2_2110_, lean_object* v_f_2111_, lean_object* v_keys_2112_, lean_object* v_vals_2113_, lean_object* v_heq_2114_, lean_object* v_i_2115_, lean_object* v_acc_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(v_00_u03c3_2108_, v_00_u03b1_2109_, v_00_u03b2_2110_, v_f_2111_, v_keys_2112_, v_vals_2113_, v_heq_2114_, v_i_2115_, v_acc_2116_);
lean_dec_ref(v_vals_2113_);
lean_dec_ref(v_keys_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14(lean_object* v_00_u03b1_2118_, lean_object* v_ref_2119_, lean_object* v_msg_2120_, lean_object* v_declHint_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(v_ref_2119_, v_msg_2120_, v_declHint_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_ref_2129_, lean_object* v_msg_2130_, lean_object* v_declHint_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14(v_00_u03b1_2128_, v_ref_2129_, v_msg_2130_, v_declHint_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_ref_2129_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19(lean_object* v_msg_2138_, lean_object* v_declHint_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(v_msg_2138_, v_declHint_2139_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___boxed(lean_object* v_msg_2146_, lean_object* v_declHint_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19(v_msg_2146_, v_declHint_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_2154_, lean_object* v_ref_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(v_ref_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_ref_2164_, lean_object* v_msg_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17(v_00_u03b1_2163_, v_ref_2164_, v_msg_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v_ref_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21(lean_object* v_00_u03b1_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21(v_00_u03b1_2180_, v_msg_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object* v_tacticName_2188_, lean_object* v_expectedType_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___x_2195_; 
lean_inc_ref(v_expectedType_2189_);
v___x_2195_ = l_Lean_Meta_mkDecideProof(v_expectedType_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; uint8_t v_transparency_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___y_2202_; uint8_t v___x_2263_; uint8_t v___x_2264_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l_Lean_Meta_Context_config(v_a_2190_);
v_transparency_2198_ = lean_ctor_get_uint8(v___x_2197_, 9);
v___x_2199_ = l_Lean_Expr_appFn_x21(v_a_2196_);
v___x_2200_ = l_Lean_Expr_appArg_x21(v___x_2199_);
lean_dec_ref(v___x_2199_);
v___x_2263_ = 1;
v___x_2264_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2198_, v___x_2263_);
if (v___x_2264_ == 0)
{
v___y_2202_ = v_transparency_2198_;
goto v___jp_2201_;
}
else
{
v___y_2202_ = v___x_2263_;
goto v___jp_2201_;
}
v___jp_2201_:
{
uint8_t v_foApprox_2203_; uint8_t v_ctxApprox_2204_; uint8_t v_quasiPatternApprox_2205_; uint8_t v_constApprox_2206_; uint8_t v_isDefEqStuckEx_2207_; uint8_t v_unificationHints_2208_; uint8_t v_proofIrrelevance_2209_; uint8_t v_assignSyntheticOpaque_2210_; uint8_t v_offsetCnstrs_2211_; uint8_t v_etaStruct_2212_; uint8_t v_univApprox_2213_; uint8_t v_iota_2214_; uint8_t v_beta_2215_; uint8_t v_proj_2216_; uint8_t v_zeta_2217_; uint8_t v_zetaDelta_2218_; uint8_t v_zetaUnused_2219_; uint8_t v_zetaHave_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2262_; 
v_foApprox_2203_ = lean_ctor_get_uint8(v___x_2197_, 0);
v_ctxApprox_2204_ = lean_ctor_get_uint8(v___x_2197_, 1);
v_quasiPatternApprox_2205_ = lean_ctor_get_uint8(v___x_2197_, 2);
v_constApprox_2206_ = lean_ctor_get_uint8(v___x_2197_, 3);
v_isDefEqStuckEx_2207_ = lean_ctor_get_uint8(v___x_2197_, 4);
v_unificationHints_2208_ = lean_ctor_get_uint8(v___x_2197_, 5);
v_proofIrrelevance_2209_ = lean_ctor_get_uint8(v___x_2197_, 6);
v_assignSyntheticOpaque_2210_ = lean_ctor_get_uint8(v___x_2197_, 7);
v_offsetCnstrs_2211_ = lean_ctor_get_uint8(v___x_2197_, 8);
v_etaStruct_2212_ = lean_ctor_get_uint8(v___x_2197_, 10);
v_univApprox_2213_ = lean_ctor_get_uint8(v___x_2197_, 11);
v_iota_2214_ = lean_ctor_get_uint8(v___x_2197_, 12);
v_beta_2215_ = lean_ctor_get_uint8(v___x_2197_, 13);
v_proj_2216_ = lean_ctor_get_uint8(v___x_2197_, 14);
v_zeta_2217_ = lean_ctor_get_uint8(v___x_2197_, 15);
v_zetaDelta_2218_ = lean_ctor_get_uint8(v___x_2197_, 16);
v_zetaUnused_2219_ = lean_ctor_get_uint8(v___x_2197_, 17);
v_zetaHave_2220_ = lean_ctor_get_uint8(v___x_2197_, 18);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2222_ = v___x_2197_;
v_isShared_2223_ = v_isSharedCheck_2262_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v___x_2197_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2262_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
uint8_t v_trackZetaDelta_2224_; lean_object* v_zetaDeltaSet_2225_; lean_object* v_lctx_2226_; lean_object* v_localInstances_2227_; lean_object* v_defEqCtx_x3f_2228_; lean_object* v_synthPendingDepth_2229_; lean_object* v_canUnfold_x3f_2230_; uint8_t v_univApprox_2231_; uint8_t v_inTypeClassResolution_2232_; uint8_t v_cacheInferType_2233_; lean_object* v_config_2235_; 
v_trackZetaDelta_2224_ = lean_ctor_get_uint8(v_a_2190_, sizeof(void*)*7);
v_zetaDeltaSet_2225_ = lean_ctor_get(v_a_2190_, 1);
v_lctx_2226_ = lean_ctor_get(v_a_2190_, 2);
v_localInstances_2227_ = lean_ctor_get(v_a_2190_, 3);
v_defEqCtx_x3f_2228_ = lean_ctor_get(v_a_2190_, 4);
v_synthPendingDepth_2229_ = lean_ctor_get(v_a_2190_, 5);
v_canUnfold_x3f_2230_ = lean_ctor_get(v_a_2190_, 6);
v_univApprox_2231_ = lean_ctor_get_uint8(v_a_2190_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2232_ = lean_ctor_get_uint8(v_a_2190_, sizeof(void*)*7 + 2);
v_cacheInferType_2233_ = lean_ctor_get_uint8(v_a_2190_, sizeof(void*)*7 + 3);
if (v_isShared_2223_ == 0)
{
v_config_2235_ = v___x_2222_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 0, v_foApprox_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 1, v_ctxApprox_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 2, v_quasiPatternApprox_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 3, v_constApprox_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 4, v_isDefEqStuckEx_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 5, v_unificationHints_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 6, v_proofIrrelevance_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 7, v_assignSyntheticOpaque_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 8, v_offsetCnstrs_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 10, v_etaStruct_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 11, v_univApprox_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 12, v_iota_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 13, v_beta_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 14, v_proj_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 15, v_zeta_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 16, v_zetaDelta_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 17, v_zetaUnused_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, 18, v_zetaHave_2220_);
v_config_2235_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
uint64_t v___x_2236_; uint64_t v___x_2237_; uint64_t v___x_2238_; uint64_t v___x_2239_; uint64_t v___x_2240_; uint64_t v_key_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_ctor_set_uint8(v_config_2235_, 9, v___y_2202_);
v___x_2236_ = l_Lean_Meta_Context_configKey(v_a_2190_);
v___x_2237_ = 2ULL;
v___x_2238_ = lean_uint64_shift_right(v___x_2236_, v___x_2237_);
v___x_2239_ = lean_uint64_shift_left(v___x_2238_, v___x_2237_);
v___x_2240_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2202_);
v_key_2241_ = lean_uint64_lor(v___x_2239_, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2242_, 0, v_config_2235_);
lean_ctor_set_uint64(v___x_2242_, sizeof(void*)*1, v_key_2241_);
lean_inc(v_canUnfold_x3f_2230_);
lean_inc(v_synthPendingDepth_2229_);
lean_inc(v_defEqCtx_x3f_2228_);
lean_inc_ref(v_localInstances_2227_);
lean_inc_ref(v_lctx_2226_);
lean_inc(v_zetaDeltaSet_2225_);
v___x_2243_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v_zetaDeltaSet_2225_);
lean_ctor_set(v___x_2243_, 2, v_lctx_2226_);
lean_ctor_set(v___x_2243_, 3, v_localInstances_2227_);
lean_ctor_set(v___x_2243_, 4, v_defEqCtx_x3f_2228_);
lean_ctor_set(v___x_2243_, 5, v_synthPendingDepth_2229_);
lean_ctor_set(v___x_2243_, 6, v_canUnfold_x3f_2230_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*7, v_trackZetaDelta_2224_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*7 + 1, v_univApprox_2231_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2232_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*7 + 3, v_cacheInferType_2233_);
lean_inc(v_a_2193_);
lean_inc_ref(v_a_2192_);
lean_inc(v_a_2191_);
lean_inc_ref(v___x_2200_);
v___x_2244_ = lean_whnf(v___x_2200_, v___x_2243_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2260_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2260_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2260_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5));
v___x_2250_ = l_Lean_Expr_isAppOf(v_a_2245_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_del_object(v___x_2247_);
lean_dec(v_a_2196_);
lean_inc_ref(v_expectedType_2189_);
v___x_2251_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed), 9, 4);
lean_closure_set(v___x_2251_, 0, v_tacticName_2188_);
lean_closure_set(v___x_2251_, 1, v_expectedType_2189_);
lean_closure_set(v___x_2251_, 2, v___x_2200_);
lean_closure_set(v___x_2251_, 3, v_a_2245_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_mk_empty_array_with_capacity(v___x_2252_);
v___x_2254_ = lean_array_push(v___x_2253_, v_expectedType_2189_);
v___x_2255_ = l_Lean_MessageData_ofLazyM(v___x_2251_, v___x_2254_);
v___x_2256_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2255_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2256_;
}
else
{
lean_object* v___x_2258_; 
lean_dec(v_a_2245_);
lean_dec_ref(v___x_2200_);
lean_dec_ref(v_expectedType_2189_);
lean_dec(v_tacticName_2188_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_a_2196_);
v___x_2258_ = v___x_2247_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2196_);
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
lean_dec_ref(v___x_2200_);
lean_dec(v_a_2196_);
lean_dec_ref(v_expectedType_2189_);
lean_dec(v_tacticName_2188_);
return v___x_2244_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2189_);
lean_dec(v_tacticName_2188_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(lean_object* v_tacticName_2265_, lean_object* v_expectedType_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2265_, v_expectedType_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* v_tacticName_2273_, lean_object* v_expectedType_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2273_, v_expectedType_2274_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* v_tacticName_2285_, lean_object* v_expectedType_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(v_tacticName_2285_, v_expectedType_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(lean_object* v___x_2303_, lean_object* v_tacticName_2304_, lean_object* v_expectedType_2305_, uint8_t v___x_2306_, lean_object* v_a_2307_, uint8_t v___x_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v___y_2315_; lean_object* v___x_2393_; uint8_t v_transparency_2394_; uint8_t v___x_2395_; 
v___x_2393_ = l_Lean_Meta_Context_config(v___y_2309_);
v_transparency_2394_ = lean_ctor_get_uint8(v___x_2393_, 9);
lean_dec_ref(v___x_2393_);
v___x_2395_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2394_, v___x_2308_);
if (v___x_2395_ == 0)
{
v___y_2315_ = v_transparency_2394_;
goto v___jp_2314_;
}
else
{
v___y_2315_ = v___x_2308_;
goto v___jp_2314_;
}
v___jp_2314_:
{
lean_object* v___x_2316_; uint8_t v_foApprox_2317_; uint8_t v_ctxApprox_2318_; uint8_t v_quasiPatternApprox_2319_; uint8_t v_constApprox_2320_; uint8_t v_isDefEqStuckEx_2321_; uint8_t v_unificationHints_2322_; uint8_t v_proofIrrelevance_2323_; uint8_t v_assignSyntheticOpaque_2324_; uint8_t v_offsetCnstrs_2325_; uint8_t v_etaStruct_2326_; uint8_t v_univApprox_2327_; uint8_t v_iota_2328_; uint8_t v_beta_2329_; uint8_t v_proj_2330_; uint8_t v_zeta_2331_; uint8_t v_zetaDelta_2332_; uint8_t v_zetaUnused_2333_; uint8_t v_zetaHave_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2392_; 
v___x_2316_ = l_Lean_Meta_Context_config(v___y_2309_);
v_foApprox_2317_ = lean_ctor_get_uint8(v___x_2316_, 0);
v_ctxApprox_2318_ = lean_ctor_get_uint8(v___x_2316_, 1);
v_quasiPatternApprox_2319_ = lean_ctor_get_uint8(v___x_2316_, 2);
v_constApprox_2320_ = lean_ctor_get_uint8(v___x_2316_, 3);
v_isDefEqStuckEx_2321_ = lean_ctor_get_uint8(v___x_2316_, 4);
v_unificationHints_2322_ = lean_ctor_get_uint8(v___x_2316_, 5);
v_proofIrrelevance_2323_ = lean_ctor_get_uint8(v___x_2316_, 6);
v_assignSyntheticOpaque_2324_ = lean_ctor_get_uint8(v___x_2316_, 7);
v_offsetCnstrs_2325_ = lean_ctor_get_uint8(v___x_2316_, 8);
v_etaStruct_2326_ = lean_ctor_get_uint8(v___x_2316_, 10);
v_univApprox_2327_ = lean_ctor_get_uint8(v___x_2316_, 11);
v_iota_2328_ = lean_ctor_get_uint8(v___x_2316_, 12);
v_beta_2329_ = lean_ctor_get_uint8(v___x_2316_, 13);
v_proj_2330_ = lean_ctor_get_uint8(v___x_2316_, 14);
v_zeta_2331_ = lean_ctor_get_uint8(v___x_2316_, 15);
v_zetaDelta_2332_ = lean_ctor_get_uint8(v___x_2316_, 16);
v_zetaUnused_2333_ = lean_ctor_get_uint8(v___x_2316_, 17);
v_zetaHave_2334_ = lean_ctor_get_uint8(v___x_2316_, 18);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2336_ = v___x_2316_;
v_isShared_2337_ = v_isSharedCheck_2392_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v___x_2316_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2392_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint8_t v_trackZetaDelta_2338_; lean_object* v_zetaDeltaSet_2339_; lean_object* v_lctx_2340_; lean_object* v_localInstances_2341_; lean_object* v_defEqCtx_x3f_2342_; lean_object* v_synthPendingDepth_2343_; lean_object* v_canUnfold_x3f_2344_; uint8_t v_univApprox_2345_; uint8_t v_inTypeClassResolution_2346_; uint8_t v_cacheInferType_2347_; lean_object* v_config_2349_; 
v_trackZetaDelta_2338_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*7);
v_zetaDeltaSet_2339_ = lean_ctor_get(v___y_2309_, 1);
v_lctx_2340_ = lean_ctor_get(v___y_2309_, 2);
v_localInstances_2341_ = lean_ctor_get(v___y_2309_, 3);
v_defEqCtx_x3f_2342_ = lean_ctor_get(v___y_2309_, 4);
v_synthPendingDepth_2343_ = lean_ctor_get(v___y_2309_, 5);
v_canUnfold_x3f_2344_ = lean_ctor_get(v___y_2309_, 6);
v_univApprox_2345_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2346_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*7 + 2);
v_cacheInferType_2347_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*7 + 3);
if (v_isShared_2337_ == 0)
{
v_config_2349_ = v___x_2336_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 0, v_foApprox_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 1, v_ctxApprox_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 2, v_quasiPatternApprox_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 3, v_constApprox_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 4, v_isDefEqStuckEx_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 5, v_unificationHints_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 6, v_proofIrrelevance_2323_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 7, v_assignSyntheticOpaque_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 8, v_offsetCnstrs_2325_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 10, v_etaStruct_2326_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 11, v_univApprox_2327_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 12, v_iota_2328_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 13, v_beta_2329_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 14, v_proj_2330_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 15, v_zeta_2331_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 16, v_zetaDelta_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 17, v_zetaUnused_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2391_, 18, v_zetaHave_2334_);
v_config_2349_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
uint64_t v___x_2350_; uint64_t v___x_2351_; uint64_t v___x_2352_; uint64_t v___x_2353_; uint64_t v___x_2354_; uint64_t v_key_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_ctor_set_uint8(v_config_2349_, 9, v___y_2315_);
v___x_2350_ = l_Lean_Meta_Context_configKey(v___y_2309_);
v___x_2351_ = 2ULL;
v___x_2352_ = lean_uint64_shift_right(v___x_2350_, v___x_2351_);
v___x_2353_ = lean_uint64_shift_left(v___x_2352_, v___x_2351_);
v___x_2354_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2315_);
v_key_2355_ = lean_uint64_lor(v___x_2353_, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2356_, 0, v_config_2349_);
lean_ctor_set_uint64(v___x_2356_, sizeof(void*)*1, v_key_2355_);
lean_inc(v_canUnfold_x3f_2344_);
lean_inc(v_synthPendingDepth_2343_);
lean_inc(v_defEqCtx_x3f_2342_);
lean_inc_ref(v_localInstances_2341_);
lean_inc_ref(v_lctx_2340_);
lean_inc(v_zetaDeltaSet_2339_);
v___x_2357_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v_zetaDeltaSet_2339_);
lean_ctor_set(v___x_2357_, 2, v_lctx_2340_);
lean_ctor_set(v___x_2357_, 3, v_localInstances_2341_);
lean_ctor_set(v___x_2357_, 4, v_defEqCtx_x3f_2342_);
lean_ctor_set(v___x_2357_, 5, v_synthPendingDepth_2343_);
lean_ctor_set(v___x_2357_, 6, v_canUnfold_x3f_2344_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*7, v_trackZetaDelta_2338_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*7 + 1, v_univApprox_2345_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2346_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*7 + 3, v_cacheInferType_2347_);
lean_inc(v___y_2312_);
lean_inc_ref(v___y_2311_);
lean_inc(v___y_2310_);
lean_inc_ref(v___x_2303_);
v___x_2358_ = lean_whnf(v___x_2303_, v___x_2357_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2382_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2382_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2382_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5));
v___x_2364_ = l_Lean_Expr_isAppOf(v_a_2359_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_del_object(v___x_2361_);
lean_dec_ref(v_a_2307_);
v___x_2365_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_2304_, v_expectedType_2305_, v___x_2303_, v_a_2359_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec(v_a_2359_);
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
lean_dec(v_a_2359_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v_expectedType_2305_);
lean_dec_ref(v___x_2303_);
v___x_2366_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2367_ = l_Lean_MessageData_ofName(v_tacticName_2304_);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2));
v___x_2372_ = l_Lean_MessageData_ofConstName(v___x_2371_, v___x_2306_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2370_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_Exception_toMessageData(v_a_2307_);
v___x_2377_ = l_Lean_indentD(v___x_2376_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2375_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2378_);
v___x_2380_ = v___x_2361_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
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
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v_a_2307_);
lean_dec_ref(v_expectedType_2305_);
lean_dec(v_tacticName_2304_);
lean_dec_ref(v___x_2303_);
v_a_2383_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2358_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2358_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(lean_object* v___x_2396_, lean_object* v_tacticName_2397_, lean_object* v_expectedType_2398_, lean_object* v___x_2399_, lean_object* v_a_2400_, lean_object* v___x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
uint8_t v___x_5937__boxed_2407_; uint8_t v___x_5939__boxed_2408_; lean_object* v_res_2409_; 
v___x_5937__boxed_2407_ = lean_unbox(v___x_2399_);
v___x_5939__boxed_2408_ = lean_unbox(v___x_2401_);
v_res_2409_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(v___x_2396_, v_tacticName_2397_, v_expectedType_2398_, v___x_5937__boxed_2407_, v_a_2400_, v___x_5939__boxed_2408_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec_ref(v___y_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(lean_object* v_a_2410_, lean_object* v_as_2411_, size_t v_i_2412_, size_t v_stop_2413_){
_start:
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_usize_dec_eq(v_i_2412_, v_stop_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = lean_array_uget_borrowed(v_as_2411_, v_i_2412_);
v___x_2416_ = lean_name_eq(v_a_2410_, v___x_2415_);
if (v___x_2416_ == 0)
{
size_t v___x_2417_; size_t v___x_2418_; 
v___x_2417_ = ((size_t)1ULL);
v___x_2418_ = lean_usize_add(v_i_2412_, v___x_2417_);
v_i_2412_ = v___x_2418_;
goto _start;
}
else
{
return v___x_2416_;
}
}
else
{
uint8_t v___x_2420_; 
v___x_2420_ = 0;
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(lean_object* v_a_2421_, lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_stop_2424_){
_start:
{
size_t v_i_boxed_2425_; size_t v_stop_boxed_2426_; uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_i_boxed_2425_ = lean_unbox_usize(v_i_2423_);
lean_dec(v_i_2423_);
v_stop_boxed_2426_ = lean_unbox_usize(v_stop_2424_);
lean_dec(v_stop_2424_);
v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2421_, v_as_2422_, v_i_boxed_2425_, v_stop_boxed_2426_);
lean_dec_ref(v_as_2422_);
lean_dec(v_a_2421_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object* v_as_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = lean_array_get_size(v_as_2429_);
v___x_2433_ = lean_nat_dec_lt(v___x_2431_, v___x_2432_);
if (v___x_2433_ == 0)
{
return v___x_2433_;
}
else
{
if (v___x_2433_ == 0)
{
return v___x_2433_;
}
else
{
size_t v___x_2434_; size_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2434_ = ((size_t)0ULL);
v___x_2435_ = lean_usize_of_nat(v___x_2432_);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_2430_, v_as_2429_, v___x_2434_, v___x_2435_);
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object* v_as_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v_as_2437_, v_a_2438_);
lean_dec(v_a_2438_);
lean_dec_ref(v_as_2437_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(lean_object* v___x_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
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
lean_object* v_head_2445_; lean_object* v_tail_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2456_; 
v_head_2445_ = lean_ctor_get(v_a_2442_, 0);
v_tail_2446_ = lean_ctor_get(v_a_2442_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_a_2442_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2448_ = v_a_2442_;
v_isShared_2449_ = v_isSharedCheck_2456_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_tail_2446_);
lean_inc(v_head_2445_);
lean_dec(v_a_2442_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2456_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v___x_2450_; 
v___x_2450_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v___x_2441_, v_head_2445_);
if (v___x_2450_ == 0)
{
lean_del_object(v___x_2448_);
lean_dec(v_head_2445_);
v_a_2442_ = v_tail_2446_;
goto _start;
}
else
{
lean_object* v___x_2453_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v_a_2443_);
v___x_2453_ = v___x_2448_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_head_2445_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_a_2443_);
v___x_2453_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
v_a_2442_ = v_tail_2446_;
v_a_2443_ = v___x_2453_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(lean_object* v___x_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v___x_2457_, v_a_2458_, v_a_2459_);
lean_dec_ref(v___x_2457_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
if (lean_obj_tag(v_a_2461_) == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = l_List_reverse___redArg(v_a_2462_);
return v___x_2463_;
}
else
{
lean_object* v_head_2464_; lean_object* v_tail_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2474_; 
v_head_2464_ = lean_ctor_get(v_a_2461_, 0);
v_tail_2465_ = lean_ctor_get(v_a_2461_, 1);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_a_2461_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2467_ = v_a_2461_;
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_tail_2465_);
lean_inc(v_head_2464_);
lean_dec(v_a_2461_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = l_Lean_Level_param___override(v_head_2464_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 1, v_a_2462_);
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_a_2462_);
v___x_2471_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v_a_2461_ = v_tail_2465_;
v_a_2462_ = v___x_2471_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_unsigned_to_nat(16u);
v___x_2477_ = lean_mk_array(v___x_2476_, v___x_2475_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2478_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2482_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1);
v___x_2483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
lean_ctor_set(v___x_2483_, 2, v___x_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object* v_tacticName_2484_, lean_object* v_expectedType_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v___x_2494_; 
lean_inc_ref(v_expectedType_2485_);
v___x_2494_ = l_Lean_Meta_mkDecideProof(v_expectedType_2485_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = l_Lean_Elab_Term_getLevelNames___redArg(v_a_2488_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2498_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_2486_, v_a_2488_, v_a_2490_, v_a_2492_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2613_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2613_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2613_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v_params_2506_; lean_object* v_fileName_2507_; lean_object* v_fileMap_2508_; lean_object* v_options_2509_; lean_object* v_currRecDepth_2510_; lean_object* v_ref_2511_; lean_object* v_currNamespace_2512_; lean_object* v_openDecls_2513_; lean_object* v_initHeartbeats_2514_; lean_object* v_maxHeartbeats_2515_; lean_object* v_quotContext_2516_; lean_object* v_currMacroScope_2517_; lean_object* v_cancelTk_x3f_2518_; uint8_t v_suppressElabErrors_2519_; lean_object* v_inheritedTraceOptions_2520_; lean_object* v_env_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; uint8_t v___x_2529_; lean_object* v___y_2531_; uint8_t v___y_2532_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v_fileName_2559_; lean_object* v_fileMap_2560_; lean_object* v_currRecDepth_2561_; lean_object* v_ref_2562_; lean_object* v_currNamespace_2563_; lean_object* v_openDecls_2564_; lean_object* v_initHeartbeats_2565_; lean_object* v_maxHeartbeats_2566_; lean_object* v_quotContext_2567_; lean_object* v_currMacroScope_2568_; lean_object* v_cancelTk_x3f_2569_; uint8_t v_suppressElabErrors_2570_; lean_object* v_inheritedTraceOptions_2571_; lean_object* v___y_2572_; uint8_t v___y_2591_; uint8_t v___x_2612_; 
v___x_2503_ = lean_st_ref_get(v_a_2492_);
v___x_2504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2);
lean_inc_ref(v_expectedType_2485_);
v___x_2505_ = l_Lean_collectLevelParams(v___x_2504_, v_expectedType_2485_);
v_params_2506_ = lean_ctor_get(v___x_2505_, 2);
lean_inc_ref(v_params_2506_);
lean_dec_ref(v___x_2505_);
v_fileName_2507_ = lean_ctor_get(v_a_2491_, 0);
v_fileMap_2508_ = lean_ctor_get(v_a_2491_, 1);
v_options_2509_ = lean_ctor_get(v_a_2491_, 2);
v_currRecDepth_2510_ = lean_ctor_get(v_a_2491_, 3);
v_ref_2511_ = lean_ctor_get(v_a_2491_, 5);
v_currNamespace_2512_ = lean_ctor_get(v_a_2491_, 6);
v_openDecls_2513_ = lean_ctor_get(v_a_2491_, 7);
v_initHeartbeats_2514_ = lean_ctor_get(v_a_2491_, 8);
v_maxHeartbeats_2515_ = lean_ctor_get(v_a_2491_, 9);
v_quotContext_2516_ = lean_ctor_get(v_a_2491_, 10);
v_currMacroScope_2517_ = lean_ctor_get(v_a_2491_, 11);
v_cancelTk_x3f_2518_ = lean_ctor_get(v_a_2491_, 12);
v_suppressElabErrors_2519_ = lean_ctor_get_uint8(v_a_2491_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2520_ = lean_ctor_get(v_a_2491_, 13);
v_env_2521_ = lean_ctor_get(v___x_2503_, 0);
lean_inc_ref(v_env_2521_);
lean_dec(v___x_2503_);
v___x_2522_ = l_Lean_Expr_appFn_x21(v_a_2495_);
v___x_2523_ = l_Lean_Expr_appArg_x21(v___x_2522_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = l_List_reverse___redArg(v_a_2497_);
v___x_2525_ = lean_box(0);
v___x_2526_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v_params_2506_, v___x_2524_, v___x_2525_);
lean_dec_ref(v_params_2506_);
v___x_2527_ = lean_box(0);
v___x_2528_ = 1;
v___x_2529_ = 0;
v___x_2554_ = l_Lean_Elab_async;
lean_inc_ref(v_options_2509_);
v___x_2555_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_2509_, v___x_2554_, v___x_2529_);
v___x_2556_ = l_Lean_diagnostics;
v___x_2557_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_2555_, v___x_2556_);
v___x_2612_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2521_);
lean_dec_ref(v_env_2521_);
if (v___x_2612_ == 0)
{
if (v___x_2557_ == 0)
{
v_fileName_2559_ = v_fileName_2507_;
v_fileMap_2560_ = v_fileMap_2508_;
v_currRecDepth_2561_ = v_currRecDepth_2510_;
v_ref_2562_ = v_ref_2511_;
v_currNamespace_2563_ = v_currNamespace_2512_;
v_openDecls_2564_ = v_openDecls_2513_;
v_initHeartbeats_2565_ = v_initHeartbeats_2514_;
v_maxHeartbeats_2566_ = v_maxHeartbeats_2515_;
v_quotContext_2567_ = v_quotContext_2516_;
v_currMacroScope_2568_ = v_currMacroScope_2517_;
v_cancelTk_x3f_2569_ = v_cancelTk_x3f_2518_;
v_suppressElabErrors_2570_ = v_suppressElabErrors_2519_;
v_inheritedTraceOptions_2571_ = v_inheritedTraceOptions_2520_;
v___y_2572_ = v_a_2492_;
goto v___jp_2558_;
}
else
{
v___y_2591_ = v___x_2612_;
goto v___jp_2590_;
}
}
else
{
v___y_2591_ = v___x_2557_;
goto v___jp_2590_;
}
v___jp_2530_:
{
if (v___y_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_del_object(v___x_2501_);
v___x_2533_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2499_, v___y_2532_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2533_) == 0)
{
uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v___x_2533_);
v___x_2534_ = 1;
v___x_2535_ = lean_box(v___x_2529_);
v___x_2536_ = lean_box(v___x_2534_);
lean_inc_ref(v_expectedType_2485_);
v___f_2537_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2537_, 0, v___x_2523_);
lean_closure_set(v___f_2537_, 1, v_tacticName_2484_);
lean_closure_set(v___f_2537_, 2, v_expectedType_2485_);
lean_closure_set(v___f_2537_, 3, v___x_2535_);
lean_closure_set(v___f_2537_, 4, v___y_2531_);
lean_closure_set(v___f_2537_, 5, v___x_2536_);
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = lean_mk_empty_array_with_capacity(v___x_2538_);
v___x_2540_ = lean_array_push(v___x_2539_, v_expectedType_2485_);
v___x_2541_ = l_Lean_MessageData_ofLazyM(v___f_2537_, v___x_2540_);
v___x_2542_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2541_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
return v___x_2542_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___x_2523_);
lean_dec_ref(v_expectedType_2485_);
lean_dec(v_tacticName_2484_);
v_a_2543_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2533_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2533_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v___x_2552_; 
lean_dec_ref(v___x_2523_);
lean_dec(v_a_2499_);
lean_dec_ref(v_expectedType_2485_);
lean_dec(v_tacticName_2484_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
lean_ctor_set(v___x_2501_, 0, v___y_2531_);
v___x_2552_ = v___x_2501_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___y_2531_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
v___jp_2558_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2573_ = l_Lean_maxRecDepth;
v___x_2574_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_2555_, v___x_2573_);
lean_inc_ref(v_inheritedTraceOptions_2571_);
lean_inc(v_cancelTk_x3f_2569_);
lean_inc(v_currMacroScope_2568_);
lean_inc(v_quotContext_2567_);
lean_inc(v_maxHeartbeats_2566_);
lean_inc(v_initHeartbeats_2565_);
lean_inc(v_openDecls_2564_);
lean_inc(v_currNamespace_2563_);
lean_inc(v_ref_2562_);
lean_inc(v_currRecDepth_2561_);
lean_inc_ref(v_fileMap_2560_);
lean_inc_ref(v_fileName_2559_);
v___x_2575_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2575_, 0, v_fileName_2559_);
lean_ctor_set(v___x_2575_, 1, v_fileMap_2560_);
lean_ctor_set(v___x_2575_, 2, v___x_2555_);
lean_ctor_set(v___x_2575_, 3, v_currRecDepth_2561_);
lean_ctor_set(v___x_2575_, 4, v___x_2574_);
lean_ctor_set(v___x_2575_, 5, v_ref_2562_);
lean_ctor_set(v___x_2575_, 6, v_currNamespace_2563_);
lean_ctor_set(v___x_2575_, 7, v_openDecls_2564_);
lean_ctor_set(v___x_2575_, 8, v_initHeartbeats_2565_);
lean_ctor_set(v___x_2575_, 9, v_maxHeartbeats_2566_);
lean_ctor_set(v___x_2575_, 10, v_quotContext_2567_);
lean_ctor_set(v___x_2575_, 11, v_currMacroScope_2568_);
lean_ctor_set(v___x_2575_, 12, v_cancelTk_x3f_2569_);
lean_ctor_set(v___x_2575_, 13, v_inheritedTraceOptions_2571_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*14, v___x_2557_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*14 + 1, v_suppressElabErrors_2570_);
lean_inc_ref(v_expectedType_2485_);
lean_inc(v___x_2526_);
v___x_2576_ = l_Lean_Meta_mkAuxLemma(v___x_2526_, v_expectedType_2485_, v_a_2495_, v___x_2527_, v___x_2528_, v___x_2529_, v___x_2529_, v___x_2529_, v_a_2489_, v_a_2490_, v___x_2575_, v___y_2572_);
lean_dec_ref(v___x_2575_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v___x_2523_);
lean_del_object(v___x_2501_);
lean_dec(v_a_2499_);
lean_dec_ref(v_expectedType_2485_);
lean_dec(v_tacticName_2484_);
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2586_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2586_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2581_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(v___x_2526_, v___x_2525_);
v___x_2582_ = l_Lean_mkConst(v_a_2577_, v___x_2581_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2582_);
v___x_2584_ = v___x_2579_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2587_; uint8_t v___x_2588_; 
lean_dec(v___x_2526_);
v_a_2587_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2576_);
v___x_2588_ = l_Lean_Exception_isInterrupt(v_a_2587_);
if (v___x_2588_ == 0)
{
uint8_t v___x_2589_; 
lean_inc(v_a_2587_);
v___x_2589_ = l_Lean_Exception_isRuntime(v_a_2587_);
v___y_2531_ = v_a_2587_;
v___y_2532_ = v___x_2589_;
goto v___jp_2530_;
}
else
{
v___y_2531_ = v_a_2587_;
v___y_2532_ = v___x_2588_;
goto v___jp_2530_;
}
}
}
v___jp_2590_:
{
if (v___y_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v_env_2593_; lean_object* v_nextMacroScope_2594_; lean_object* v_ngen_2595_; lean_object* v_auxDeclNGen_2596_; lean_object* v_traceState_2597_; lean_object* v_messages_2598_; lean_object* v_infoState_2599_; lean_object* v_snapshotTasks_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2610_; 
v___x_2592_ = lean_st_ref_take(v_a_2492_);
v_env_2593_ = lean_ctor_get(v___x_2592_, 0);
v_nextMacroScope_2594_ = lean_ctor_get(v___x_2592_, 1);
v_ngen_2595_ = lean_ctor_get(v___x_2592_, 2);
v_auxDeclNGen_2596_ = lean_ctor_get(v___x_2592_, 3);
v_traceState_2597_ = lean_ctor_get(v___x_2592_, 4);
v_messages_2598_ = lean_ctor_get(v___x_2592_, 6);
v_infoState_2599_ = lean_ctor_get(v___x_2592_, 7);
v_snapshotTasks_2600_ = lean_ctor_get(v___x_2592_, 8);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; 
v_unused_2611_ = lean_ctor_get(v___x_2592_, 5);
lean_dec(v_unused_2611_);
v___x_2602_ = v___x_2592_;
v_isShared_2603_ = v_isSharedCheck_2610_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_snapshotTasks_2600_);
lean_inc(v_infoState_2599_);
lean_inc(v_messages_2598_);
lean_inc(v_traceState_2597_);
lean_inc(v_auxDeclNGen_2596_);
lean_inc(v_ngen_2595_);
lean_inc(v_nextMacroScope_2594_);
lean_inc(v_env_2593_);
lean_dec(v___x_2592_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2610_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2604_ = l_Lean_Kernel_enableDiag(v_env_2593_, v___x_2557_);
v___x_2605_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 5, v___x_2605_);
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2607_ = v___x_2602_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_nextMacroScope_2594_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v_ngen_2595_);
lean_ctor_set(v_reuseFailAlloc_2609_, 3, v_auxDeclNGen_2596_);
lean_ctor_set(v_reuseFailAlloc_2609_, 4, v_traceState_2597_);
lean_ctor_set(v_reuseFailAlloc_2609_, 5, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2609_, 6, v_messages_2598_);
lean_ctor_set(v_reuseFailAlloc_2609_, 7, v_infoState_2599_);
lean_ctor_set(v_reuseFailAlloc_2609_, 8, v_snapshotTasks_2600_);
v___x_2607_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_st_ref_set(v_a_2492_, v___x_2607_);
v_fileName_2559_ = v_fileName_2507_;
v_fileMap_2560_ = v_fileMap_2508_;
v_currRecDepth_2561_ = v_currRecDepth_2510_;
v_ref_2562_ = v_ref_2511_;
v_currNamespace_2563_ = v_currNamespace_2512_;
v_openDecls_2564_ = v_openDecls_2513_;
v_initHeartbeats_2565_ = v_initHeartbeats_2514_;
v_maxHeartbeats_2566_ = v_maxHeartbeats_2515_;
v_quotContext_2567_ = v_quotContext_2516_;
v_currMacroScope_2568_ = v_currMacroScope_2517_;
v_cancelTk_x3f_2569_ = v_cancelTk_x3f_2518_;
v_suppressElabErrors_2570_ = v_suppressElabErrors_2519_;
v_inheritedTraceOptions_2571_ = v_inheritedTraceOptions_2520_;
v___y_2572_ = v_a_2492_;
goto v___jp_2558_;
}
}
}
else
{
v_fileName_2559_ = v_fileName_2507_;
v_fileMap_2560_ = v_fileMap_2508_;
v_currRecDepth_2561_ = v_currRecDepth_2510_;
v_ref_2562_ = v_ref_2511_;
v_currNamespace_2563_ = v_currNamespace_2512_;
v_openDecls_2564_ = v_openDecls_2513_;
v_initHeartbeats_2565_ = v_initHeartbeats_2514_;
v_maxHeartbeats_2566_ = v_maxHeartbeats_2515_;
v_quotContext_2567_ = v_quotContext_2516_;
v_currMacroScope_2568_ = v_currMacroScope_2517_;
v_cancelTk_x3f_2569_ = v_cancelTk_x3f_2518_;
v_suppressElabErrors_2570_ = v_suppressElabErrors_2519_;
v_inheritedTraceOptions_2571_ = v_inheritedTraceOptions_2520_;
v___y_2572_ = v_a_2492_;
goto v___jp_2558_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec_ref(v_expectedType_2485_);
lean_dec(v_tacticName_2484_);
v_a_2614_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2498_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2498_);
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
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2495_);
lean_dec_ref(v_expectedType_2485_);
lean_dec(v_tacticName_2484_);
v_a_2622_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2496_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2496_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2485_);
lean_dec(v_tacticName_2484_);
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object* v_tacticName_2630_, lean_object* v_expectedType_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2630_, v_expectedType_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* v_tacticName_2641_, lean_object* v_expectedType_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2641_, v_expectedType_2642_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* v_tacticName_2653_, lean_object* v_expectedType_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(v_tacticName_2653_, v_expectedType_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
return v_res_2664_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0));
v___x_2667_ = l_Lean_stringToMessageData(v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t v_native_2668_, uint8_t v_kernel_2669_, lean_object* v_tacticName_2670_, lean_object* v_expectedType_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; 
if (v_kernel_2669_ == 0)
{
v___y_2683_ = v___y_2673_;
v___y_2684_ = v___y_2674_;
v___y_2685_ = v___y_2675_;
v___y_2686_ = v___y_2676_;
v___y_2687_ = v___y_2677_;
v___y_2688_ = v___y_2678_;
v___y_2689_ = v___y_2679_;
v___y_2690_ = v___y_2680_;
goto v___jp_2682_;
}
else
{
if (v_native_2668_ == 0)
{
v___y_2683_ = v___y_2673_;
v___y_2684_ = v___y_2674_;
v___y_2685_ = v___y_2675_;
v___y_2686_ = v___y_2676_;
v___y_2687_ = v___y_2677_;
v___y_2688_ = v___y_2678_;
v___y_2689_ = v___y_2679_;
v___y_2690_ = v___y_2680_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_expectedType_2671_);
v___x_2698_ = lean_obj_once(&l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4, &l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once, _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4);
v___x_2699_ = l_Lean_MessageData_ofName(v_tacticName_2670_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_obj_once(&l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1, &l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_2702_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
v___jp_2682_:
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(v_expectedType_2671_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2691_) == 0)
{
if (v_native_2668_ == 0)
{
if (v_kernel_2669_ == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v___x_2693_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_2670_, v_a_2692_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2693_;
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2691_);
v___x_2695_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_2670_, v_a_2694_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2695_;
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2696_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2691_);
v___x_2697_ = l_Lean_Elab_Tactic_elabNativeDecideCore(v_tacticName_2670_, v_a_2696_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2697_;
}
}
else
{
lean_dec(v_tacticName_2670_);
return v___x_2691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object* v_native_2712_, lean_object* v_kernel_2713_, lean_object* v_tacticName_2714_, lean_object* v_expectedType_2715_, lean_object* v_x_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v_native_boxed_2726_; uint8_t v_kernel_boxed_2727_; lean_object* v_res_2728_; 
v_native_boxed_2726_ = lean_unbox(v_native_2712_);
v_kernel_boxed_2727_ = lean_unbox(v_kernel_2713_);
v_res_2728_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0(v_native_boxed_2726_, v_kernel_boxed_2727_, v_tacticName_2714_, v_expectedType_2715_, v_x_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v_x_2716_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t v_revert_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2731_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0));
v___x_2742_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_a_2740_, v___x_2741_, v_revert_2729_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc_n(v_a_2743_, 2);
lean_dec_ref(v___x_2742_);
v___x_2744_ = l_Lean_MVarId_getDecl(v_a_2743_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v_lctx_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v_lctx_2746_ = lean_ctor_get(v_a_2745_, 1);
lean_inc_ref(v_lctx_2746_);
lean_dec(v_a_2745_);
v___x_2747_ = l_Lean_LocalContext_getFVarIds(v_lctx_2746_);
lean_dec_ref(v_lctx_2746_);
v___x_2748_ = 0;
v___x_2749_ = l_Lean_MVarId_revert(v_a_2743_, v___x_2747_, v___x_2748_, v_revert_2729_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v_snd_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2760_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
v_snd_2751_ = lean_ctor_get(v_a_2750_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_a_2750_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v_a_2750_, 0);
lean_dec(v_unused_2761_);
v___x_2753_ = v_a_2750_;
v_isShared_2754_ = v_isSharedCheck_2760_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snd_2751_);
lean_dec(v_a_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2760_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = lean_box(0);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 1);
lean_ctor_set(v___x_2753_, 1, v___x_2755_);
lean_ctor_set(v___x_2753_, 0, v_snd_2751_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_snd_2751_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2757_, v___y_2731_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2749_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2749_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2743_);
v_a_2770_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2744_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2744_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2742_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2742_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2739_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2739_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object* v_revert_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
uint8_t v_revert_boxed_2804_; lean_object* v_res_2805_; 
v_revert_boxed_2804_ = lean_unbox(v_revert_2794_);
v_res_2805_ = l_Lean_Elab_Tactic_evalDecideCore___lam__1(v_revert_boxed_2804_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* v_tacticName_2806_, lean_object* v_cfg_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
uint8_t v_kernel_2817_; uint8_t v_native_2818_; uint8_t v_revert_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___f_2822_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; 
v_kernel_2817_ = lean_ctor_get_uint8(v_cfg_2807_, 0);
v_native_2818_ = lean_ctor_get_uint8(v_cfg_2807_, 1);
v_revert_2819_ = lean_ctor_get_uint8(v_cfg_2807_, 3);
v___x_2820_ = lean_box(v_native_2818_);
v___x_2821_ = lean_box(v_kernel_2817_);
lean_inc(v_tacticName_2806_);
v___f_2822_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2822_, 0, v___x_2820_);
lean_closure_set(v___f_2822_, 1, v___x_2821_);
lean_closure_set(v___f_2822_, 2, v_tacticName_2806_);
if (v_revert_2819_ == 0)
{
v___y_2824_ = v_a_2808_;
v___y_2825_ = v_a_2809_;
v___y_2826_ = v_a_2810_;
v___y_2827_ = v_a_2811_;
v___y_2828_ = v_a_2812_;
v___y_2829_ = v_a_2813_;
v___y_2830_ = v_a_2814_;
v___y_2831_ = v_a_2815_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; 
v___x_2834_ = lean_box(v_revert_2819_);
v___f_2835_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2835_, 0, v___x_2834_);
v___x_2836_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2835_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_dec_ref(v___x_2836_);
v___y_2824_ = v_a_2808_;
v___y_2825_ = v_a_2809_;
v___y_2826_ = v_a_2810_;
v___y_2827_ = v_a_2811_;
v___y_2828_ = v_a_2812_;
v___y_2829_ = v_a_2813_;
v___y_2830_ = v_a_2814_;
v___y_2831_ = v_a_2815_;
goto v___jp_2823_;
}
else
{
lean_dec_ref(v___f_2822_);
lean_dec(v_tacticName_2806_);
return v___x_2836_;
}
}
v___jp_2823_:
{
uint8_t v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = 1;
v___x_2833_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacticName_2806_, v___f_2822_, v___x_2832_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object* v_tacticName_2837_, lean_object* v_cfg_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_Tactic_evalDecideCore(v_tacticName_2837_, v_cfg_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec_ref(v_cfg_2838_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(lean_object* v_e_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v___x_2864_; uint8_t v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2864_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_2865_ = 0;
v___x_2866_ = 1;
v___x_2867_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_2864_, v_e_2858_, v___x_2865_, v___x_2866_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3____boxed(lean_object* v_e_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v_e_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(lean_object* v_e_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v_e_2875_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3____boxed(lean_object* v_e_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v_e_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2893_, lean_object* v_x_2894_){
_start:
{
if (lean_obj_tag(v_x_2894_) == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_box(0);
return v___x_2895_;
}
else
{
lean_object* v_key_2896_; lean_object* v_value_2897_; lean_object* v_tail_2898_; uint8_t v___x_2899_; 
v_key_2896_ = lean_ctor_get(v_x_2894_, 0);
v_value_2897_ = lean_ctor_get(v_x_2894_, 1);
v_tail_2898_ = lean_ctor_get(v_x_2894_, 2);
v___x_2899_ = lean_name_eq(v_key_2896_, v_a_2893_);
if (v___x_2899_ == 0)
{
v_x_2894_ = v_tail_2898_;
goto _start;
}
else
{
lean_object* v___x_2901_; 
lean_inc(v_value_2897_);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_value_2897_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg(v_a_2902_, v_x_2903_);
lean_dec(v_x_2903_);
lean_dec(v_a_2902_);
return v_res_2904_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2905_; uint64_t v___x_2906_; 
v___x_2905_ = lean_unsigned_to_nat(1723u);
v___x_2906_ = lean_uint64_of_nat(v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(lean_object* v_m_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_buckets_2909_; lean_object* v___x_2910_; uint64_t v___y_2912_; 
v_buckets_2909_ = lean_ctor_get(v_m_2907_, 1);
v___x_2910_ = lean_array_get_size(v_buckets_2909_);
if (lean_obj_tag(v_a_2908_) == 0)
{
uint64_t v___x_2926_; 
v___x_2926_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___closed__0);
v___y_2912_ = v___x_2926_;
goto v___jp_2911_;
}
else
{
uint64_t v_hash_2927_; 
v_hash_2927_ = lean_ctor_get_uint64(v_a_2908_, sizeof(void*)*2);
v___y_2912_ = v_hash_2927_;
goto v___jp_2911_;
}
v___jp_2911_:
{
uint64_t v___x_2913_; uint64_t v___x_2914_; uint64_t v_fold_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; size_t v___x_2919_; size_t v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2913_ = 32ULL;
v___x_2914_ = lean_uint64_shift_right(v___y_2912_, v___x_2913_);
v_fold_2915_ = lean_uint64_xor(v___y_2912_, v___x_2914_);
v___x_2916_ = 16ULL;
v___x_2917_ = lean_uint64_shift_right(v_fold_2915_, v___x_2916_);
v___x_2918_ = lean_uint64_xor(v_fold_2915_, v___x_2917_);
v___x_2919_ = lean_uint64_to_usize(v___x_2918_);
v___x_2920_ = lean_usize_of_nat(v___x_2910_);
v___x_2921_ = ((size_t)1ULL);
v___x_2922_ = lean_usize_sub(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_usize_land(v___x_2919_, v___x_2922_);
v___x_2924_ = lean_array_uget_borrowed(v_buckets_2909_, v___x_2923_);
v___x_2925_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg(v_a_2908_, v___x_2924_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(v_m_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_m_2928_);
return v_res_2930_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2931_; double v___x_2932_; 
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_float_of_nat(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_2934_, lean_object* v_msg_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_ref_2941_; lean_object* v___x_2942_; lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2987_; 
v_ref_2941_ = lean_ctor_get(v___y_2938_, 5);
v___x_2942_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2987_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2987_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v_traceState_2948_; lean_object* v_env_2949_; lean_object* v_nextMacroScope_2950_; lean_object* v_ngen_2951_; lean_object* v_auxDeclNGen_2952_; lean_object* v_cache_2953_; lean_object* v_messages_2954_; lean_object* v_infoState_2955_; lean_object* v_snapshotTasks_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2986_; 
v___x_2947_ = lean_st_ref_take(v___y_2939_);
v_traceState_2948_ = lean_ctor_get(v___x_2947_, 4);
v_env_2949_ = lean_ctor_get(v___x_2947_, 0);
v_nextMacroScope_2950_ = lean_ctor_get(v___x_2947_, 1);
v_ngen_2951_ = lean_ctor_get(v___x_2947_, 2);
v_auxDeclNGen_2952_ = lean_ctor_get(v___x_2947_, 3);
v_cache_2953_ = lean_ctor_get(v___x_2947_, 5);
v_messages_2954_ = lean_ctor_get(v___x_2947_, 6);
v_infoState_2955_ = lean_ctor_get(v___x_2947_, 7);
v_snapshotTasks_2956_ = lean_ctor_get(v___x_2947_, 8);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2958_ = v___x_2947_;
v_isShared_2959_ = v_isSharedCheck_2986_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snapshotTasks_2956_);
lean_inc(v_infoState_2955_);
lean_inc(v_messages_2954_);
lean_inc(v_cache_2953_);
lean_inc(v_traceState_2948_);
lean_inc(v_auxDeclNGen_2952_);
lean_inc(v_ngen_2951_);
lean_inc(v_nextMacroScope_2950_);
lean_inc(v_env_2949_);
lean_dec(v___x_2947_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2986_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
uint64_t v_tid_2960_; lean_object* v_traces_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2985_; 
v_tid_2960_ = lean_ctor_get_uint64(v_traceState_2948_, sizeof(void*)*1);
v_traces_2961_ = lean_ctor_get(v_traceState_2948_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_traceState_2948_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2963_ = v_traceState_2948_;
v_isShared_2964_ = v_isSharedCheck_2985_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_traces_2961_);
lean_dec(v_traceState_2948_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2985_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; double v___x_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2965_ = lean_box(0);
v___x_2966_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_2967_ = 0;
v___x_2968_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2969_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2969_, 0, v_cls_2934_);
lean_ctor_set(v___x_2969_, 1, v___x_2965_);
lean_ctor_set(v___x_2969_, 2, v___x_2968_);
lean_ctor_set_float(v___x_2969_, sizeof(void*)*3, v___x_2966_);
lean_ctor_set_float(v___x_2969_, sizeof(void*)*3 + 8, v___x_2966_);
lean_ctor_set_uint8(v___x_2969_, sizeof(void*)*3 + 16, v___x_2967_);
v___x_2970_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0));
v___x_2971_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v_a_2943_);
lean_ctor_set(v___x_2971_, 2, v___x_2970_);
lean_inc(v_ref_2941_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_ref_2941_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = l_Lean_PersistentArray_push___redArg(v_traces_2961_, v___x_2972_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2973_);
v___x_2975_ = v___x_2963_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2973_);
lean_ctor_set_uint64(v_reuseFailAlloc_2984_, sizeof(void*)*1, v_tid_2960_);
v___x_2975_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 4, v___x_2975_);
v___x_2977_ = v___x_2958_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_env_2949_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_nextMacroScope_2950_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v_ngen_2951_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v_auxDeclNGen_2952_);
lean_ctor_set(v_reuseFailAlloc_2983_, 4, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2983_, 5, v_cache_2953_);
lean_ctor_set(v_reuseFailAlloc_2983_, 6, v_messages_2954_);
lean_ctor_set(v_reuseFailAlloc_2983_, 7, v_infoState_2955_);
lean_ctor_set(v_reuseFailAlloc_2983_, 8, v_snapshotTasks_2956_);
v___x_2977_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2978_ = lean_st_ref_set(v___y_2939_, v___x_2977_);
v___x_2979_ = lean_box(0);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2979_);
v___x_2981_ = v___x_2945_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2979_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_2988_, lean_object* v_msg_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_2988_, v_msg_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_2996_, lean_object* v_i_2997_, lean_object* v_k_2998_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = lean_array_get_size(v_keys_2996_);
v___x_3000_ = lean_nat_dec_lt(v_i_2997_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec(v_i_2997_);
return v___x_3000_;
}
else
{
lean_object* v_k_x27_3001_; uint8_t v___x_3002_; 
v_k_x27_3001_ = lean_array_fget_borrowed(v_keys_2996_, v_i_2997_);
v___x_3002_ = l_Lean_instBEqExtraModUse_beq(v_k_2998_, v_k_x27_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_unsigned_to_nat(1u);
v___x_3004_ = lean_nat_add(v_i_2997_, v___x_3003_);
lean_dec(v_i_2997_);
v_i_2997_ = v___x_3004_;
goto _start;
}
else
{
lean_dec(v_i_2997_);
return v___x_3002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_3006_, lean_object* v_i_3007_, lean_object* v_k_3008_){
_start:
{
uint8_t v_res_3009_; lean_object* v_r_3010_; 
v_res_3009_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_keys_3006_, v_i_3007_, v_k_3008_);
lean_dec_ref(v_k_3008_);
lean_dec_ref(v_keys_3006_);
v_r_3010_ = lean_box(v_res_3009_);
return v_r_3010_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_3011_; size_t v___x_3012_; size_t v___x_3013_; 
v___x_3011_ = ((size_t)5ULL);
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_shift_left(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; 
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_3016_ = lean_usize_sub(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_3017_, size_t v_x_3018_, lean_object* v_x_3019_){
_start:
{
if (lean_obj_tag(v_x_3017_) == 0)
{
lean_object* v_es_3020_; lean_object* v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; lean_object* v_j_3025_; lean_object* v___x_3026_; 
v_es_3020_ = lean_ctor_get(v_x_3017_, 0);
v___x_3021_ = lean_box(2);
v___x_3022_ = ((size_t)5ULL);
v___x_3023_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_3024_ = lean_usize_land(v_x_3018_, v___x_3023_);
v_j_3025_ = lean_usize_to_nat(v___x_3024_);
v___x_3026_ = lean_array_get_borrowed(v___x_3021_, v_es_3020_, v_j_3025_);
lean_dec(v_j_3025_);
switch(lean_obj_tag(v___x_3026_))
{
case 0:
{
lean_object* v_key_3027_; uint8_t v___x_3028_; 
v_key_3027_ = lean_ctor_get(v___x_3026_, 0);
v___x_3028_ = l_Lean_instBEqExtraModUse_beq(v_x_3019_, v_key_3027_);
return v___x_3028_;
}
case 1:
{
lean_object* v_node_3029_; size_t v___x_3030_; 
v_node_3029_ = lean_ctor_get(v___x_3026_, 0);
v___x_3030_ = lean_usize_shift_right(v_x_3018_, v___x_3022_);
v_x_3017_ = v_node_3029_;
v_x_3018_ = v___x_3030_;
goto _start;
}
default: 
{
uint8_t v___x_3032_; 
v___x_3032_ = 0;
return v___x_3032_;
}
}
}
else
{
lean_object* v_ks_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_ks_3033_ = lean_ctor_get(v_x_3017_, 0);
v___x_3034_ = lean_unsigned_to_nat(0u);
v___x_3035_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ks_3033_, v___x_3034_, v_x_3019_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
size_t v_x_10613__boxed_3039_; uint8_t v_res_3040_; lean_object* v_r_3041_; 
v_x_10613__boxed_3039_ = lean_unbox_usize(v_x_3037_);
lean_dec(v_x_3037_);
v_res_3040_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3036_, v_x_10613__boxed_3039_, v_x_3038_);
lean_dec_ref(v_x_3038_);
lean_dec_ref(v_x_3036_);
v_r_3041_ = lean_box(v_res_3040_);
return v_r_3041_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3042_, lean_object* v_x_3043_){
_start:
{
uint64_t v___x_3044_; size_t v___x_3045_; uint8_t v___x_3046_; 
v___x_3044_ = l_Lean_instHashableExtraModUse_hash(v_x_3043_);
v___x_3045_ = lean_uint64_to_usize(v___x_3044_);
v___x_3046_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3042_, v___x_3045_, v_x_3043_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3047_, lean_object* v_x_3048_){
_start:
{
uint8_t v_res_3049_; lean_object* v_r_3050_; 
v_res_3049_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_3047_, v_x_3048_);
lean_dec_ref(v_x_3048_);
lean_dec_ref(v_x_3047_);
v_r_3050_ = lean_box(v_res_3049_);
return v_r_3050_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__1));
v___x_3054_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__0));
v___x_3055_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3054_, v___x_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5);
v___x_3057_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
lean_ctor_set(v___x_3057_, 2, v___x_3056_);
lean_ctor_set(v___x_3057_, 3, v___x_3056_);
lean_ctor_set(v___x_3057_, 4, v___x_3056_);
lean_ctor_set(v___x_3057_, 5, v___x_3056_);
return v___x_3057_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__6));
v___x_3063_ = l_Lean_stringToMessageData(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__8));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_3068_ = l_Lean_stringToMessageData(v___x_3067_);
return v___x_3068_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v_cls_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_cls_3069_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__5));
v___x_3070_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1));
v___x_3071_ = l_Lean_Name_append(v___x_3070_, v_cls_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__12));
v___x_3074_ = l_Lean_stringToMessageData(v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(lean_object* v_mod_3079_, uint8_t v_isMeta_3080_, lean_object* v_hint_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; lean_object* v_env_3090_; uint8_t v_isExporting_3091_; lean_object* v___x_3092_; lean_object* v_env_3093_; lean_object* v___x_3094_; lean_object* v_entry_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3089_ = lean_st_ref_get(v___y_3087_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_ref(v_env_3090_);
lean_dec(v___x_3089_);
v_isExporting_3091_ = lean_ctor_get_uint8(v_env_3090_, sizeof(void*)*8);
lean_dec_ref(v_env_3090_);
v___x_3092_ = lean_st_ref_get(v___y_3087_);
v_env_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc_ref(v_env_3093_);
lean_dec(v___x_3092_);
v___x_3094_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_3079_);
v_entry_3095_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3095_, 0, v_mod_3079_);
lean_ctor_set_uint8(v_entry_3095_, sizeof(void*)*1, v_isExporting_3091_);
lean_ctor_set_uint8(v_entry_3095_, sizeof(void*)*1 + 1, v_isMeta_3080_);
v___x_3096_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3097_ = lean_box(1);
v___x_3098_ = lean_box(0);
v___x_3141_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3094_, v___x_3096_, v_env_3093_, v___x_3097_, v___x_3098_);
v___x_3142_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(v___x_3141_, v_entry_3095_);
lean_dec(v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v_options_3143_; uint8_t v_hasTrace_3144_; 
v_options_3143_ = lean_ctor_get(v___y_3086_, 2);
v_hasTrace_3144_ = lean_ctor_get_uint8(v_options_3143_, sizeof(void*)*1);
if (v_hasTrace_3144_ == 0)
{
lean_dec(v_hint_3081_);
lean_dec(v_mod_3079_);
v___y_3100_ = v___y_3085_;
v___y_3101_ = v___y_3087_;
goto v___jp_3099_;
}
else
{
lean_object* v_inheritedTraceOptions_3145_; lean_object* v_cls_3146_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_inheritedTraceOptions_3145_ = lean_ctor_get(v___y_3086_, 13);
v_cls_3146_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__5));
v___x_3166_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__11);
v___x_3167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3145_, v_options_3143_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_dec(v_hint_3081_);
lean_dec(v_mod_3079_);
v___y_3100_ = v___y_3085_;
v___y_3101_ = v___y_3087_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3168_; lean_object* v___y_3170_; 
v___x_3168_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__13);
if (v_isExporting_3091_ == 0)
{
lean_object* v___x_3177_; 
v___x_3177_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__16));
v___y_3170_ = v___x_3177_;
goto v___jp_3169_;
}
else
{
lean_object* v___x_3178_; 
v___x_3178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__17));
v___y_3170_ = v___x_3178_;
goto v___jp_3169_;
}
v___jp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_inc_ref(v___y_3170_);
v___x_3171_ = l_Lean_stringToMessageData(v___y_3170_);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3168_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
if (v_isMeta_3080_ == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__14));
v___y_3153_ = v___x_3174_;
v___y_3154_ = v___x_3175_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3176_; 
v___x_3176_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__15));
v___y_3153_ = v___x_3174_;
v___y_3154_ = v___x_3176_;
goto v___jp_3152_;
}
}
}
v___jp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___y_3148_);
lean_ctor_set(v___x_3150_, 1, v___y_3149_);
v___x_3151_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_3146_, v___x_3150_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_dec_ref(v___x_3151_);
v___y_3100_ = v___y_3085_;
v___y_3101_ = v___y_3087_;
goto v___jp_3099_;
}
else
{
lean_dec_ref(v_entry_3095_);
return v___x_3151_;
}
}
v___jp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
lean_inc_ref(v___y_3154_);
v___x_3155_ = l_Lean_stringToMessageData(v___y_3154_);
v___x_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___y_3153_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__7);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_MessageData_ofName(v_mod_3079_);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = l_Lean_Name_isAnonymous(v_hint_3081_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__9);
v___x_3163_ = l_Lean_MessageData_ofName(v_hint_3081_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___y_3148_ = v___x_3160_;
v___y_3149_ = v___x_3164_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3165_; 
lean_dec(v_hint_3081_);
v___x_3165_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__10);
v___y_3148_ = v___x_3160_;
v___y_3149_ = v___x_3165_;
goto v___jp_3147_;
}
}
}
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec_ref(v_entry_3095_);
lean_dec(v_hint_3081_);
lean_dec(v_mod_3079_);
v___x_3179_ = lean_box(0);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
return v___x_3180_;
}
v___jp_3099_:
{
lean_object* v___x_3102_; lean_object* v_toEnvExtension_3103_; lean_object* v_env_3104_; lean_object* v_nextMacroScope_3105_; lean_object* v_ngen_3106_; lean_object* v_auxDeclNGen_3107_; lean_object* v_traceState_3108_; lean_object* v_messages_3109_; lean_object* v_infoState_3110_; lean_object* v_snapshotTasks_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3139_; 
v___x_3102_ = lean_st_ref_take(v___y_3101_);
v_toEnvExtension_3103_ = lean_ctor_get(v___x_3096_, 0);
v_env_3104_ = lean_ctor_get(v___x_3102_, 0);
v_nextMacroScope_3105_ = lean_ctor_get(v___x_3102_, 1);
v_ngen_3106_ = lean_ctor_get(v___x_3102_, 2);
v_auxDeclNGen_3107_ = lean_ctor_get(v___x_3102_, 3);
v_traceState_3108_ = lean_ctor_get(v___x_3102_, 4);
v_messages_3109_ = lean_ctor_get(v___x_3102_, 6);
v_infoState_3110_ = lean_ctor_get(v___x_3102_, 7);
v_snapshotTasks_3111_ = lean_ctor_get(v___x_3102_, 8);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_3102_, 5);
lean_dec(v_unused_3140_);
v___x_3113_ = v___x_3102_;
v_isShared_3114_ = v_isSharedCheck_3139_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_snapshotTasks_3111_);
lean_inc(v_infoState_3110_);
lean_inc(v_messages_3109_);
lean_inc(v_traceState_3108_);
lean_inc(v_auxDeclNGen_3107_);
lean_inc(v_ngen_3106_);
lean_inc(v_nextMacroScope_3105_);
lean_inc(v_env_3104_);
lean_dec(v___x_3102_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3139_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_asyncMode_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v_asyncMode_3115_ = lean_ctor_get(v_toEnvExtension_3103_, 2);
v___x_3116_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3096_, v_env_3104_, v_entry_3095_, v_asyncMode_3115_, v___x_3098_);
v___x_3117_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 5, v___x_3117_);
lean_ctor_set(v___x_3113_, 0, v___x_3116_);
v___x_3119_ = v___x_3113_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_nextMacroScope_3105_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_ngen_3106_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_auxDeclNGen_3107_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_traceState_3108_);
lean_ctor_set(v_reuseFailAlloc_3138_, 5, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3138_, 6, v_messages_3109_);
lean_ctor_set(v_reuseFailAlloc_3138_, 7, v_infoState_3110_);
lean_ctor_set(v_reuseFailAlloc_3138_, 8, v_snapshotTasks_3111_);
v___x_3119_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v_mctx_3122_; lean_object* v_zetaDeltaFVarIds_3123_; lean_object* v_postponed_3124_; lean_object* v_diag_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3136_; 
v___x_3120_ = lean_st_ref_set(v___y_3101_, v___x_3119_);
v___x_3121_ = lean_st_ref_take(v___y_3100_);
v_mctx_3122_ = lean_ctor_get(v___x_3121_, 0);
v_zetaDeltaFVarIds_3123_ = lean_ctor_get(v___x_3121_, 2);
v_postponed_3124_ = lean_ctor_get(v___x_3121_, 3);
v_diag_3125_ = lean_ctor_get(v___x_3121_, 4);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3121_, 1);
lean_dec(v_unused_3137_);
v___x_3127_ = v___x_3121_;
v_isShared_3128_ = v_isSharedCheck_3136_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_diag_3125_);
lean_inc(v_postponed_3124_);
lean_inc(v_zetaDeltaFVarIds_3123_);
lean_inc(v_mctx_3122_);
lean_dec(v___x_3121_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3136_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___closed__3);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3129_);
v___x_3131_ = v___x_3127_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_mctx_3122_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_zetaDeltaFVarIds_3123_);
lean_ctor_set(v_reuseFailAlloc_3135_, 3, v_postponed_3124_);
lean_ctor_set(v_reuseFailAlloc_3135_, 4, v_diag_3125_);
v___x_3131_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = lean_st_ref_set(v___y_3100_, v___x_3131_);
v___x_3133_ = lean_box(0);
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
return v___x_3134_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0___boxed(lean_object* v_mod_3181_, lean_object* v_isMeta_3182_, lean_object* v_hint_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
uint8_t v_isMeta_boxed_3191_; lean_object* v_res_3192_; 
v_isMeta_boxed_3191_ = lean_unbox(v_isMeta_3182_);
v_res_3192_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(v_mod_3181_, v_isMeta_boxed_3191_, v_hint_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(lean_object* v___x_3193_, lean_object* v_declName_3194_, lean_object* v_as_3195_, size_t v_sz_3196_, size_t v_i_3197_, lean_object* v_b_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
uint8_t v___x_3206_; 
v___x_3206_ = lean_usize_dec_lt(v_i_3197_, v_sz_3196_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
lean_dec(v_declName_3194_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_b_3198_);
return v___x_3207_;
}
else
{
lean_object* v___x_3208_; lean_object* v_modules_3209_; lean_object* v___x_3210_; lean_object* v_a_3211_; lean_object* v___x_3212_; lean_object* v_toImport_3213_; lean_object* v_module_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3208_ = l_Lean_Environment_header(v___x_3193_);
v_modules_3209_ = lean_ctor_get(v___x_3208_, 3);
lean_inc_ref(v_modules_3209_);
lean_dec_ref(v___x_3208_);
v___x_3210_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3211_ = lean_array_uget_borrowed(v_as_3195_, v_i_3197_);
v___x_3212_ = lean_array_get(v___x_3210_, v_modules_3209_, v_a_3211_);
lean_dec_ref(v_modules_3209_);
v_toImport_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc_ref(v_toImport_3213_);
lean_dec(v___x_3212_);
v_module_3214_ = lean_ctor_get(v_toImport_3213_, 0);
lean_inc(v_module_3214_);
lean_dec_ref(v_toImport_3213_);
v___x_3215_ = 0;
lean_inc(v_declName_3194_);
v___x_3216_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(v_module_3214_, v___x_3215_, v_declName_3194_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; 
lean_dec_ref(v___x_3216_);
v___x_3217_ = lean_box(0);
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_add(v_i_3197_, v___x_3218_);
v_i_3197_ = v___x_3219_;
v_b_3198_ = v___x_3217_;
goto _start;
}
else
{
lean_dec(v_declName_3194_);
return v___x_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1___boxed(lean_object* v___x_3221_, lean_object* v_declName_3222_, lean_object* v_as_3223_, lean_object* v_sz_3224_, lean_object* v_i_3225_, lean_object* v_b_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
size_t v_sz_boxed_3234_; size_t v_i_boxed_3235_; lean_object* v_res_3236_; 
v_sz_boxed_3234_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v_i_boxed_3235_ = lean_unbox_usize(v_i_3225_);
lean_dec(v_i_3225_);
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(v___x_3221_, v_declName_3222_, v_as_3223_, v_sz_boxed_3234_, v_i_boxed_3235_, v_b_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v_as_3223_);
lean_dec_ref(v___x_3221_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__1));
v___x_3240_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__0));
v___x_3241_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3240_, v___x_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(lean_object* v_declName_3244_, uint8_t v_isMeta_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; lean_object* v_env_3257_; lean_object* v___y_3259_; lean_object* v___x_3272_; 
v___x_3253_ = lean_st_ref_get(v___y_3251_);
v_env_3257_ = lean_ctor_get(v___x_3253_, 0);
lean_inc_ref(v_env_3257_);
lean_dec(v___x_3253_);
v___x_3272_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3257_, v_declName_3244_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_dec_ref(v_env_3257_);
lean_dec(v_declName_3244_);
goto v___jp_3254_;
}
else
{
lean_object* v_val_3273_; lean_object* v___x_3274_; lean_object* v_modules_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v_val_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_val_3273_);
lean_dec_ref(v___x_3272_);
v___x_3274_ = l_Lean_Environment_header(v_env_3257_);
v_modules_3275_ = lean_ctor_get(v___x_3274_, 3);
lean_inc_ref(v_modules_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = lean_array_get_size(v_modules_3275_);
v___x_3277_ = lean_nat_dec_lt(v_val_3273_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_dec_ref(v_modules_3275_);
lean_dec(v_val_3273_);
lean_dec_ref(v_env_3257_);
lean_dec(v_declName_3244_);
goto v___jp_3254_;
}
else
{
lean_object* v___x_3278_; lean_object* v_env_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___y_3283_; 
v___x_3278_ = lean_st_ref_get(v___y_3251_);
v_env_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc_ref(v_env_3279_);
lean_dec(v___x_3278_);
v___x_3280_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__2);
v___x_3281_ = lean_array_fget(v_modules_3275_, v_val_3273_);
lean_dec(v_val_3273_);
lean_dec_ref(v_modules_3275_);
if (v_isMeta_3245_ == 0)
{
lean_dec_ref(v_env_3279_);
v___y_3283_ = v_isMeta_3245_;
goto v___jp_3282_;
}
else
{
uint8_t v___x_3294_; 
lean_inc(v_declName_3244_);
v___x_3294_ = l_Lean_isMarkedMeta(v_env_3279_, v_declName_3244_);
if (v___x_3294_ == 0)
{
v___y_3283_ = v_isMeta_3245_;
goto v___jp_3282_;
}
else
{
uint8_t v___x_3295_; 
v___x_3295_ = 0;
v___y_3283_ = v___x_3295_;
goto v___jp_3282_;
}
}
v___jp_3282_:
{
lean_object* v_toImport_3284_; lean_object* v_module_3285_; lean_object* v___x_3286_; 
v_toImport_3284_ = lean_ctor_get(v___x_3281_, 0);
lean_inc_ref(v_toImport_3284_);
lean_dec(v___x_3281_);
v_module_3285_ = lean_ctor_get(v_toImport_3284_, 0);
lean_inc(v_module_3285_);
lean_dec_ref(v_toImport_3284_);
lean_inc(v_declName_3244_);
v___x_3286_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0(v_module_3285_, v___y_3283_, v_declName_3244_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec_ref(v___x_3286_);
v___x_3287_ = l_Lean_indirectModUseExt;
v___x_3288_ = lean_box(1);
v___x_3289_ = lean_box(0);
lean_inc_ref(v_env_3257_);
v___x_3290_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3280_, v___x_3287_, v_env_3257_, v___x_3288_, v___x_3289_);
v___x_3291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(v___x_3290_, v_declName_3244_);
lean_dec(v___x_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v___x_3292_; 
v___x_3292_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___closed__3));
v___y_3259_ = v___x_3292_;
goto v___jp_3258_;
}
else
{
lean_object* v_val_3293_; 
v_val_3293_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_val_3293_);
lean_dec_ref(v___x_3291_);
v___y_3259_ = v_val_3293_;
goto v___jp_3258_;
}
}
else
{
lean_dec_ref(v_env_3257_);
lean_dec(v_declName_3244_);
return v___x_3286_;
}
}
}
}
v___jp_3254_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
v___jp_3258_:
{
lean_object* v___x_3260_; size_t v_sz_3261_; size_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3260_ = lean_box(0);
v_sz_3261_ = lean_array_size(v___y_3259_);
v___x_3262_ = ((size_t)0ULL);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__1(v_env_3257_, v_declName_3244_, v___y_3259_, v_sz_3261_, v___x_3262_, v___x_3260_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_env_3257_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3270_ == 0)
{
lean_object* v_unused_3271_; 
v_unused_3271_ = lean_ctor_get(v___x_3263_, 0);
lean_dec(v_unused_3271_);
v___x_3265_ = v___x_3263_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_dec(v___x_3263_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3260_);
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3260_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
else
{
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0___boxed(lean_object* v_declName_3296_, lean_object* v_isMeta_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
uint8_t v_isMeta_boxed_3305_; lean_object* v_res_3306_; 
v_isMeta_boxed_3305_ = lean_unbox(v_isMeta_3297_);
v_res_3306_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(v_declName_3296_, v_isMeta_boxed_3305_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2));
v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4));
v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6));
v___x_3318_ = l_Lean_stringToMessageData(v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_3320_ = l_Lean_MessageData_ofName(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8);
v___x_3322_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v___x_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object* v_optConfig_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; uint8_t v_recover_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; uint8_t v___x_3374_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; 
v_recover_3368_ = lean_ctor_get_uint8(v_a_3328_, sizeof(void*)*1);
lean_inc(v_optConfig_3327_);
v___x_3369_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_3327_);
v___x_3370_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_3369_);
v___x_3371_ = lean_array_get_size(v___x_3370_);
v___x_3372_ = lean_unsigned_to_nat(0u);
v___x_3373_ = lean_nat_dec_eq(v___x_3371_, v___x_3372_);
v___x_3374_ = 1;
if (v___x_3373_ == 0)
{
lean_object* v___x_3422_; lean_object* v_fileName_3423_; lean_object* v_fileMap_3424_; lean_object* v_options_3425_; lean_object* v_currRecDepth_3426_; lean_object* v_maxRecDepth_3427_; lean_object* v_ref_3428_; lean_object* v_currNamespace_3429_; lean_object* v_openDecls_3430_; lean_object* v_initHeartbeats_3431_; lean_object* v_maxHeartbeats_3432_; lean_object* v_quotContext_3433_; lean_object* v_currMacroScope_3434_; uint8_t v_diag_3435_; lean_object* v_cancelTk_x3f_3436_; uint8_t v_suppressElabErrors_3437_; lean_object* v_inheritedTraceOptions_3438_; lean_object* v_env_3439_; lean_object* v_ref_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3422_ = lean_st_ref_get(v_a_3334_);
v_fileName_3423_ = lean_ctor_get(v_a_3333_, 0);
v_fileMap_3424_ = lean_ctor_get(v_a_3333_, 1);
v_options_3425_ = lean_ctor_get(v_a_3333_, 2);
v_currRecDepth_3426_ = lean_ctor_get(v_a_3333_, 3);
v_maxRecDepth_3427_ = lean_ctor_get(v_a_3333_, 4);
v_ref_3428_ = lean_ctor_get(v_a_3333_, 5);
v_currNamespace_3429_ = lean_ctor_get(v_a_3333_, 6);
v_openDecls_3430_ = lean_ctor_get(v_a_3333_, 7);
v_initHeartbeats_3431_ = lean_ctor_get(v_a_3333_, 8);
v_maxHeartbeats_3432_ = lean_ctor_get(v_a_3333_, 9);
v_quotContext_3433_ = lean_ctor_get(v_a_3333_, 10);
v_currMacroScope_3434_ = lean_ctor_get(v_a_3333_, 11);
v_diag_3435_ = lean_ctor_get_uint8(v_a_3333_, sizeof(void*)*14);
v_cancelTk_x3f_3436_ = lean_ctor_get(v_a_3333_, 12);
v_suppressElabErrors_3437_ = lean_ctor_get_uint8(v_a_3333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3438_ = lean_ctor_get(v_a_3333_, 13);
v_env_3439_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_env_3439_);
lean_dec(v___x_3422_);
v_ref_3440_ = l_Lean_replaceRef(v_optConfig_3327_, v_ref_3428_);
lean_dec(v_optConfig_3327_);
lean_inc_ref(v_inheritedTraceOptions_3438_);
lean_inc(v_cancelTk_x3f_3436_);
lean_inc(v_currMacroScope_3434_);
lean_inc(v_quotContext_3433_);
lean_inc(v_maxHeartbeats_3432_);
lean_inc(v_initHeartbeats_3431_);
lean_inc(v_openDecls_3430_);
lean_inc(v_currNamespace_3429_);
lean_inc(v_maxRecDepth_3427_);
lean_inc(v_currRecDepth_3426_);
lean_inc_ref(v_options_3425_);
lean_inc_ref(v_fileMap_3424_);
lean_inc_ref(v_fileName_3423_);
v___x_3441_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3441_, 0, v_fileName_3423_);
lean_ctor_set(v___x_3441_, 1, v_fileMap_3424_);
lean_ctor_set(v___x_3441_, 2, v_options_3425_);
lean_ctor_set(v___x_3441_, 3, v_currRecDepth_3426_);
lean_ctor_set(v___x_3441_, 4, v_maxRecDepth_3427_);
lean_ctor_set(v___x_3441_, 5, v_ref_3440_);
lean_ctor_set(v___x_3441_, 6, v_currNamespace_3429_);
lean_ctor_set(v___x_3441_, 7, v_openDecls_3430_);
lean_ctor_set(v___x_3441_, 8, v_initHeartbeats_3431_);
lean_ctor_set(v___x_3441_, 9, v_maxHeartbeats_3432_);
lean_ctor_set(v___x_3441_, 10, v_quotContext_3433_);
lean_ctor_set(v___x_3441_, 11, v_currMacroScope_3434_);
lean_ctor_set(v___x_3441_, 12, v_cancelTk_x3f_3436_);
lean_ctor_set(v___x_3441_, 13, v_inheritedTraceOptions_3438_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*14, v_diag_3435_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*14 + 1, v_suppressElabErrors_3437_);
v___x_3442_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_3443_ = l_Lean_Environment_contains(v_env_3439_, v___x_3442_, v___x_3374_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref(v___x_3370_);
v___x_3444_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9);
v___x_3445_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3444_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v___x_3441_, v_a_3334_);
lean_dec_ref(v___x_3441_);
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
else
{
v___y_3376_ = v_a_3329_;
v___y_3377_ = v_a_3330_;
v___y_3378_ = v_a_3331_;
v___y_3379_ = v_a_3332_;
v___y_3380_ = v___x_3441_;
v___y_3381_ = v_a_3334_;
goto v___jp_3375_;
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref(v___x_3370_);
lean_dec(v_optConfig_3327_);
v___x_3454_ = ((lean_object*)(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10));
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
v___jp_3336_:
{
if (v___y_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec_ref(v___y_3343_);
v___x_3347_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1);
v___x_3348_ = l_Lean_MessageData_ofExpr(v___y_3345_);
v___x_3349_ = l_Lean_indentD(v___x_3348_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3347_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = l_Lean_Exception_toMessageData(v___y_3341_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3354_, v___y_3342_, v___y_3344_, v___y_3338_, v___y_3339_, v___y_3337_, v___y_3340_);
lean_dec_ref(v___y_3337_);
return v___x_3355_;
}
else
{
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___y_3337_);
return v___y_3343_;
}
}
v___jp_3356_:
{
lean_object* v___x_3364_; 
lean_inc_ref(v___y_3357_);
v___x_3364_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_(v___y_3357_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_dec_ref(v___y_3362_);
lean_dec_ref(v___y_3357_);
return v___x_3364_;
}
else
{
lean_object* v_a_3365_; uint8_t v___x_3366_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
v___x_3366_ = l_Lean_Exception_isInterrupt(v_a_3365_);
if (v___x_3366_ == 0)
{
uint8_t v___x_3367_; 
lean_inc(v_a_3365_);
v___x_3367_ = l_Lean_Exception_isRuntime(v_a_3365_);
v___y_3337_ = v___y_3362_;
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___y_3363_;
v___y_3341_ = v_a_3365_;
v___y_3342_ = v___y_3358_;
v___y_3343_ = v___x_3364_;
v___y_3344_ = v___y_3359_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___x_3367_;
goto v___jp_3336_;
}
else
{
v___y_3337_ = v___y_3362_;
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___y_3363_;
v___y_3341_ = v_a_3365_;
v___y_3342_ = v___y_3358_;
v___y_3343_ = v___x_3364_;
v___y_3344_ = v___y_3359_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___x_3366_;
goto v___jp_3336_;
}
}
}
v___jp_3375_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__4_00___x40_Lean_Elab_Tactic_Decide_1350635058____hygCtx___hyg_3_));
v___x_3383_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0(v___x_3382_, v___x_3374_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v___x_3383_);
v___x_3384_ = l_Lean_Elab_Tactic_elabConfig(v_recover_3368_, v___x_3382_, v___x_3370_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3405_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3405_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3405_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
uint8_t v___x_3389_; 
v___x_3389_ = l_Lean_Expr_hasSyntheticSorry(v_a_3385_);
if (v___x_3389_ == 0)
{
uint8_t v___x_3390_; 
lean_del_object(v___x_3387_);
v___x_3390_ = l_Lean_Expr_hasSorry(v_a_3385_);
if (v___x_3390_ == 0)
{
v___y_3357_ = v_a_3385_;
v___y_3358_ = v___y_3376_;
v___y_3359_ = v___y_3377_;
v___y_3360_ = v___y_3378_;
v___y_3361_ = v___y_3379_;
v___y_3362_ = v___y_3380_;
v___y_3363_ = v___y_3381_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v_a_3385_);
v___x_3391_ = lean_obj_once(&l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5);
v___x_3392_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3391_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec_ref(v___y_3380_);
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
lean_dec(v_a_3385_);
lean_dec_ref(v___y_3380_);
v___x_3401_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3401_, 0, v___x_3373_);
lean_ctor_set_uint8(v___x_3401_, 1, v___x_3373_);
lean_ctor_set_uint8(v___x_3401_, 2, v___x_3374_);
lean_ctor_set_uint8(v___x_3401_, 3, v___x_3373_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3401_);
v___x_3403_ = v___x_3387_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
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
lean_dec_ref(v___y_3380_);
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
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec_ref(v___y_3380_);
lean_dec_ref(v___x_3370_);
v_a_3414_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3383_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3383_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object* v_optConfig_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_optConfig_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec_ref(v_a_3457_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* v_optConfig_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v_optConfig_3466_, v_a_3467_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* v_optConfig_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Elab_Tactic_elabDecideConfig(v_optConfig_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2(lean_object* v_00_u03b2_3488_, lean_object* v_m_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___redArg(v_m_3489_, v_a_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3492_, lean_object* v_m_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2(v_00_u03b2_3492_, v_m_3493_, v_a_3494_);
lean_dec(v_a_3494_);
lean_dec_ref(v_m_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
uint8_t v___x_3499_; 
v___x_3499_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_3497_, v_x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3500_, lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
uint8_t v_res_3503_; lean_object* v_r_3504_; 
v_res_3503_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1(v_00_u03b2_3500_, v_x_3501_, v_x_3502_);
lean_dec_ref(v_x_3502_);
lean_dec_ref(v_x_3501_);
v_r_3504_ = lean_box(v_res_3503_);
return v_r_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3505_, lean_object* v_msg_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_3505_, v_msg_3506_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3515_, lean_object* v_msg_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__2(v_cls_3515_, v_msg_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3525_, lean_object* v_a_3526_, lean_object* v_x_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___redArg(v_a_3526_, v_x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3529_, lean_object* v_a_3530_, lean_object* v_x_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__2_spec__5(v_00_u03b2_3529_, v_a_3530_, v_x_3531_);
lean_dec(v_x_3531_);
lean_dec(v_a_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3533_, lean_object* v_x_3534_, size_t v_x_3535_, lean_object* v_x_3536_){
_start:
{
uint8_t v___x_3537_; 
v___x_3537_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3534_, v_x_3535_, v_x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_){
_start:
{
size_t v_x_11452__boxed_3542_; uint8_t v_res_3543_; lean_object* v_r_3544_; 
v_x_11452__boxed_3542_ = lean_unbox_usize(v_x_3540_);
lean_dec(v_x_3540_);
v_res_3543_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_3538_, v_x_3539_, v_x_11452__boxed_3542_, v_x_3541_);
lean_dec_ref(v_x_3541_);
lean_dec_ref(v_x_3539_);
v_r_3544_ = lean_box(v_res_3543_);
return v_r_3544_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3545_, lean_object* v_keys_3546_, lean_object* v_vals_3547_, lean_object* v_heq_3548_, lean_object* v_i_3549_, lean_object* v_k_3550_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_keys_3546_, v_i_3549_, v_k_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3552_, lean_object* v_keys_3553_, lean_object* v_vals_3554_, lean_object* v_heq_3555_, lean_object* v_i_3556_, lean_object* v_k_3557_){
_start:
{
uint8_t v_res_3558_; lean_object* v_r_3559_; 
v_res_3558_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabDecideConfig_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b2_3552_, v_keys_3553_, v_vals_3554_, v_heq_3555_, v_i_3556_, v_k_3557_);
lean_dec_ref(v_k_3557_);
lean_dec_ref(v_vals_3554_);
lean_dec_ref(v_keys_3553_);
v_r_3559_ = lean_box(v_res_3558_);
return v_r_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* v_stx_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = l_Lean_Syntax_getArg(v_stx_3563_, v___x_3573_);
v___x_3575_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3574_, v_a_3564_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref(v___x_3575_);
v___x_3577_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDecide___closed__1));
v___x_3578_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3577_, v_a_3576_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
lean_dec(v_a_3576_);
return v___x_3578_;
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
v_a_3579_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3575_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3575_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object* v_stx_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Elab_Tactic_evalDecide(v_stx_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_stx_3587_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3611_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0));
v___x_3613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3614_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
v___x_3615_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3611_, v___x_3612_, v___x_3613_, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3));
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6));
v___x_3646_ = l_Lean_addBuiltinDeclarationRanges(v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* v_stx_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = l_Lean_Syntax_getArg(v_stx_3652_, v___x_3662_);
v___x_3664_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(v___x_3663_, v_a_3653_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; uint8_t v_kernel_3666_; uint8_t v_zetaReduce_3667_; uint8_t v_revert_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3678_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3664_);
v_kernel_3666_ = lean_ctor_get_uint8(v_a_3665_, 0);
v_zetaReduce_3667_ = lean_ctor_get_uint8(v_a_3665_, 2);
v_revert_3668_ = lean_ctor_get_uint8(v_a_3665_, 3);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3665_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3670_ = v_a_3665_;
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v_a_3665_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
uint8_t v___x_3672_; lean_object* v___x_3674_; 
v___x_3672_ = 1;
if (v_isShared_3671_ == 0)
{
v___x_3674_ = v___x_3670_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, 0, v_kernel_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, 2, v_zetaReduce_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, 3, v_revert_3668_);
v___x_3674_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_ctor_set_uint8(v___x_3674_, 1, v___x_3672_);
v___x_3675_ = ((lean_object*)(l_Lean_Elab_Tactic_evalNativeDecide___closed__1));
v___x_3676_ = l_Lean_Elab_Tactic_evalDecideCore(v___x_3675_, v___x_3674_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec_ref(v___x_3674_);
return v___x_3676_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_a_3679_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3664_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3664_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object* v_stx_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Elab_Tactic_evalNativeDecide(v_stx_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
lean_dec(v_stx_3687_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3711_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1));
v___x_3713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3714_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
v___x_3715_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3711_, v___x_3712_, v___x_3713_, v___x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(lean_object* v_a_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3));
v___x_3745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6));
v___x_3746_ = l_Lean_addBuiltinDeclarationRanges(v___x_3744_, v___x_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(lean_object* v_a_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
return v_res_3748_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
