// Lean compiler output
// Module: Lean.Meta.Tactic.TryThis
// Imports: import Lean.Server.CodeActions import Lean.Meta.Tactic.ExposeNames public import Lean.Widget.UserWidget meta import Lean.Widget.UserWidget
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_pp_mvars_anonymous;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExposedNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PrettyPrinter_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Meta_Hint_textInsertionWidget;
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Meta_Hint_tryThisDiffWidget;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_sbracket(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Hint"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tryThisDiffWidget"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 179, 88, 64, 208, 112, 210, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(174, 189, 209, 40, 106, 230, 251, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "textInsertionWidget"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 179, 88, 64, 208, 112, 210, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 84, 167, 88, 42, 220, 7, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "quickfix"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TryThis"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 126, 27, 202, 77, 92, 28, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(46, 88, 15, 193, 232, 241, 126, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 141, 110, 144, 48, 21, 53, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 239, 242, 38, 18, 148, 146, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__10_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(134, 113, 30, 192, 80, 214, 160, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(186, 76, 189, 244, 199, 127, 157, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "tryThisProvider"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__12_value),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(81, 41, 66, 117, 61, 224, 165, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "No suggestions available"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Tactic did not produce expected goal"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exposeNames"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10_value),LEAN_SCALAR_PTR_LITERAL(5, 159, 188, 156, 89, 121, 163, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expose_names"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "(expose_names; "};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "found "};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = ", but the corresponding tactic failed:"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 163, .m_capacity = 163, .m_length = 162, .m_data = "\n\nIt may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions."};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exact "};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "refine "};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "\n-- ⊢ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\n-- Remaining subgoals:"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "a "};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "partial "};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try these:"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticLet__"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 155, 119, 159, 57, 105, 185, 247)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "let "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tacticHave__"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(57, 244, 114, 225, 1, 158, 79, 25)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 191, 109, 224, 169, 145, 115)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__31_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__33_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__35_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__36_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__38_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__40_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__42_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "RequestM"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__45_value),LEAN_SCALAR_PTR_LITERAL(184, 87, 7, 59, 37, 78, 138, 49)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__46_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__48_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__50_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__52_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__53_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__51_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__54_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__55_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__56_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__57_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__58_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__59_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__60_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__61_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__49_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__62_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__63_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__47_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__64_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__43_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__65_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__66_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__67_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__41_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__68_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__69_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__70_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__39_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__71_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__72_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__73_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__37_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__74_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__75_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__76_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__34_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__77_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__32_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__78_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "have : "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "have "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "have := "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "a proof"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rwRule"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 12, 102, 31, 194, 63, 248, 122)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\n-- no goals"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n-- "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__5_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rw "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21_value;
static const lean_array_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "locationHyp"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(229, 146, 67, 234, 45, 36, 143, 176)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "an applicable rewrite lemma"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4));
v___x_12_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v___x_13_ = l_Lean_Widget_addBuiltinModule(v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_14_;
v_res_14_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
return v_res_16_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1(){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1));
v___x_25_ = l_Lean_Meta_Hint_textInsertionWidget;
v___x_26_ = l_Lean_Widget_addBuiltinModule(v___x_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_27_;
v_res_27_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___boxed(lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
return v_res_29_;
}
}
lean_object* l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(lean_object* v___y_30_){
_start:
{
lean_object* v_doc_32_; lean_object* v___x_33_; 
v_doc_32_ = lean_ctor_get(v___y_30_, 1);
lean_inc_ref(v_doc_32_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v_doc_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_30_ = stack[0].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v___y_30_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___boxed(lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v___y_35_);
lean_dec_ref(v___y_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(lean_object* v___x_41_, lean_object* v_a_42_, lean_object* v_params_43_, lean_object* v___ctx_44_, lean_object* v_info_45_, lean_object* v_result_46_){
_start:
{
if (lean_obj_tag(v_info_45_) == 10)
{
lean_object* v_i_47_; lean_object* v_stx_48_; lean_object* v_value_49_; lean_object* v___x_50_; 
v_i_47_ = lean_ctor_get(v_info_45_, 0);
v_stx_48_ = lean_ctor_get(v_i_47_, 0);
v_value_49_ = lean_ctor_get(v_i_47_, 1);
v___x_50_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_49_, v___x_41_);
if (lean_obj_tag(v___x_50_) == 1)
{
lean_object* v_val_51_; lean_object* v_edit_52_; lean_object* v_codeActionTitle_53_; uint8_t v___x_54_; lean_object* v___x_55_; 
v_val_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v___x_50_, 1);
v_edit_52_ = lean_ctor_get(v_val_51_, 0);
lean_inc_ref(v_edit_52_);
v_codeActionTitle_53_ = lean_ctor_get(v_val_51_, 1);
lean_inc_ref(v_codeActionTitle_53_);
lean_dec(v_val_51_);
v___x_54_ = 0;
v___x_55_ = l_Lean_Syntax_getRange_x3f(v_stx_48_, v___x_54_);
if (lean_obj_tag(v___x_55_) == 1)
{
lean_object* v_toEditableDocumentCore_56_; lean_object* v_meta_57_; lean_object* v_val_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_92_; 
v_toEditableDocumentCore_56_ = lean_ctor_get(v_a_42_, 0);
v_meta_57_ = lean_ctor_get(v_toEditableDocumentCore_56_, 0);
v_val_58_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_92_ == 0)
{
v___x_60_ = v___x_55_;
v_isShared_61_ = v_isSharedCheck_92_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_val_58_);
lean_dec(v___x_55_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_92_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_text_62_; lean_object* v___x_63_; lean_object* v_start_64_; lean_object* v_range_65_; lean_object* v_end_66_; lean_object* v_end_67_; lean_object* v_line_68_; lean_object* v_start_69_; lean_object* v_line_70_; uint8_t v___x_71_; 
v_text_62_ = lean_ctor_get(v_meta_57_, 3);
lean_inc_ref(v_text_62_);
v___x_63_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_62_, v_val_58_);
v_start_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_start_64_);
v_range_65_ = lean_ctor_get(v_params_43_, 3);
v_end_66_ = lean_ctor_get(v_range_65_, 1);
v_end_67_ = lean_ctor_get(v___x_63_, 1);
lean_inc_ref(v_end_67_);
lean_dec_ref(v___x_63_);
v_line_68_ = lean_ctor_get(v_start_64_, 0);
lean_inc(v_line_68_);
lean_dec_ref(v_start_64_);
v_start_69_ = lean_ctor_get(v_range_65_, 0);
v_line_70_ = lean_ctor_get(v_end_66_, 0);
v___x_71_ = lean_nat_dec_le(v_line_68_, v_line_70_);
lean_dec(v_line_68_);
if (v___x_71_ == 0)
{
lean_dec_ref(v_end_67_);
lean_del_object(v___x_60_);
lean_dec_ref(v_codeActionTitle_53_);
lean_dec_ref(v_edit_52_);
lean_dec_ref(v_a_42_);
return v_result_46_;
}
else
{
lean_object* v_line_72_; lean_object* v_line_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_90_; 
v_line_72_ = lean_ctor_get(v_start_69_, 0);
v_line_73_ = lean_ctor_get(v_end_67_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_end_67_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_end_67_, 1);
lean_dec(v_unused_91_);
v___x_75_ = v_end_67_;
v_isShared_76_ = v_isSharedCheck_90_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_line_73_);
lean_dec(v_end_67_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_90_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_le(v_line_72_, v_line_73_);
lean_dec(v_line_73_);
if (v___x_77_ == 0)
{
lean_del_object(v___x_75_);
lean_del_object(v___x_60_);
lean_dec_ref(v_codeActionTitle_53_);
lean_dec_ref(v_edit_52_);
lean_dec_ref(v_a_42_);
return v_result_46_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1));
v___x_80_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_42_);
v___x_81_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_80_, v_edit_52_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_81_);
v___x_83_ = v___x_60_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_89_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_84_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_84_, 0, v___x_78_);
lean_ctor_set(v___x_84_, 1, v___x_78_);
lean_ctor_set(v___x_84_, 2, v_codeActionTitle_53_);
lean_ctor_set(v___x_84_, 3, v___x_79_);
lean_ctor_set(v___x_84_, 4, v___x_78_);
lean_ctor_set(v___x_84_, 5, v___x_78_);
lean_ctor_set(v___x_84_, 6, v___x_78_);
lean_ctor_set(v___x_84_, 7, v___x_83_);
lean_ctor_set(v___x_84_, 8, v___x_78_);
lean_ctor_set(v___x_84_, 9, v___x_78_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_78_);
lean_ctor_set(v___x_75_, 0, v___x_84_);
v___x_86_ = v___x_75_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_78_);
v___x_86_ = v_reuseFailAlloc_88_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
v___x_87_ = lean_array_push(v_result_46_, v___x_86_);
return v___x_87_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_55_);
lean_dec_ref(v_codeActionTitle_53_);
lean_dec_ref(v_edit_52_);
lean_dec_ref(v_a_42_);
return v_result_46_;
}
}
else
{
lean_dec(v___x_50_);
lean_dec_ref(v_a_42_);
return v_result_46_;
}
}
else
{
lean_dec_ref(v_a_42_);
return v_result_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed(lean_object* v___x_93_, lean_object* v_a_94_, lean_object* v_params_95_, lean_object* v___ctx_96_, lean_object* v_info_97_, lean_object* v_result_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(v___x_93_, v_a_94_, v_params_95_, v___ctx_96_, v_info_97_, v_result_98_);
lean_dec_ref(v_info_97_);
lean_dec_ref(v___ctx_96_);
lean_dec_ref(v_params_95_);
lean_dec(v___x_93_);
return v_res_99_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object* v_params_102_, lean_object* v_snap_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_119_; 
v___x_106_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
v___x_107_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v_a_104_);
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_119_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___f_112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed), 6, 3);
lean_closure_set(v___f_112_, 0, v___x_106_);
lean_closure_set(v___f_112_, 1, v_a_108_);
lean_closure_set(v___f_112_, 2, v_params_102_);
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0));
v___x_114_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_103_);
v___x_115_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_112_, v___x_113_, v___x_114_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_115_);
v___x_117_ = v___x_110_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_102_ = stack[0].m_obj;
lean_object* v_snap_103_ = stack[1].m_obj;
lean_object* v_a_104_ = stack[2].m_obj;
lean_object* v_res_120_;
v_res_120_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(v_params_102_, v_snap_103_, v_a_104_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object* v_params_121_, lean_object* v_snap_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(v_params_121_, v_snap_122_, v_a_123_);
lean_dec_ref(v_a_123_);
return v_res_125_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1(){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14));
v___x_165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed), 4, 0);
v___x_166_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_167_;
v_res_167_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___boxed(lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(lean_object* v_opts_170_, lean_object* v_opt_171_){
_start:
{
lean_object* v_name_172_; lean_object* v_defValue_173_; lean_object* v_map_174_; lean_object* v___x_175_; 
v_name_172_ = lean_ctor_get(v_opt_171_, 0);
v_defValue_173_ = lean_ctor_get(v_opt_171_, 1);
v_map_174_ = lean_ctor_get(v_opts_170_, 0);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_174_, v_name_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_inc(v_defValue_173_);
return v_defValue_173_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_175_, 1);
if (lean_obj_tag(v_val_176_) == 3)
{
lean_object* v_v_177_; 
v_v_177_ = lean_ctor_get(v_val_176_, 0);
lean_inc(v_v_177_);
lean_dec_ref_known(v_val_176_, 1);
return v_v_177_;
}
else
{
lean_dec(v_val_176_);
lean_inc(v_defValue_173_);
return v_defValue_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0___boxed(lean_object* v_opts_178_, lean_object* v_opt_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_opts_178_, v_opt_179_);
lean_dec_ref(v_opt_179_);
lean_dec_ref(v_opts_178_);
return v_res_180_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(lean_object* v_o_184_, lean_object* v_k_185_, uint8_t v_v_186_){
_start:
{
lean_object* v_map_187_; uint8_t v_hasTrace_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_202_; 
v_map_187_ = lean_ctor_get(v_o_184_, 0);
v_hasTrace_188_ = lean_ctor_get_uint8(v_o_184_, sizeof(void*)*1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_o_184_);
if (v_isSharedCheck_202_ == 0)
{
v___x_190_ = v_o_184_;
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_map_187_);
lean_dec(v_o_184_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_192_, 0, v_v_186_);
lean_inc(v_k_185_);
v___x_193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_185_, v___x_192_, v_map_187_);
if (v_hasTrace_188_ == 0)
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_197_; 
v___x_194_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__1));
v___x_195_ = l_Lean_Name_isPrefixOf(v___x_194_, v_k_185_);
lean_dec(v_k_185_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_195_);
return v___x_197_;
}
}
else
{
lean_object* v___x_200_; 
lean_dec(v_k_185_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_200_ = v___x_190_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, sizeof(void*)*1, v_hasTrace_188_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_184_ = stack[0].m_obj;
lean_object* v_k_185_ = stack[1].m_obj;
uint8_t v_v_186_ = stack[2].m_num;
lean_object* v_res_203_;
v_res_203_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(v_o_184_, v_k_185_, v_v_186_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___boxed(lean_object* v_o_204_, lean_object* v_k_205_, lean_object* v_v_206_){
_start:
{
uint8_t v_v_boxed_207_; lean_object* v_res_208_; 
v_v_boxed_207_ = lean_unbox(v_v_206_);
v_res_208_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(v_o_204_, v_k_205_, v_v_boxed_207_);
return v_res_208_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(lean_object* v_opts_209_, lean_object* v_opt_210_, uint8_t v_val_211_){
_start:
{
lean_object* v_name_212_; lean_object* v___x_213_; 
v_name_212_ = lean_ctor_get(v_opt_210_, 0);
lean_inc(v_name_212_);
lean_dec_ref(v_opt_210_);
v___x_213_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(v_opts_209_, v_name_212_, v_val_211_);
return v___x_213_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_209_ = stack[0].m_obj;
lean_object* v_opt_210_ = stack[1].m_obj;
uint8_t v_val_211_ = stack[2].m_num;
lean_object* v_res_214_;
v_res_214_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_opts_209_, v_opt_210_, v_val_211_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1___boxed(lean_object* v_opts_215_, lean_object* v_opt_216_, lean_object* v_val_217_){
_start:
{
uint8_t v_val_boxed_218_; lean_object* v_res_219_; 
v_val_boxed_218_ = lean_unbox(v_val_217_);
v_res_219_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_opts_215_, v_opt_216_, v_val_boxed_218_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object* v_e_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_toCold_231_; lean_object* v_currRecDepth_232_; lean_object* v_ref_233_; uint8_t v_suppressElabErrors_234_; uint8_t v_isRecordingDeps_235_; lean_object* v_fileName_236_; lean_object* v_fileMap_237_; lean_object* v_options_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_initHeartbeats_241_; lean_object* v_maxHeartbeats_242_; lean_object* v_quotContext_243_; lean_object* v_currMacroScope_244_; lean_object* v_cancelTk_x3f_245_; lean_object* v_inheritedTraceOptions_246_; lean_object* v___x_247_; lean_object* v___y_249_; uint16_t v___y_250_; lean_object* v_fileName_251_; lean_object* v_fileMap_252_; lean_object* v_currNamespace_253_; lean_object* v_openDecls_254_; lean_object* v_initHeartbeats_255_; lean_object* v_maxHeartbeats_256_; lean_object* v_quotContext_257_; lean_object* v_currMacroScope_258_; lean_object* v_cancelTk_x3f_259_; lean_object* v_inheritedTraceOptions_260_; lean_object* v_currRecDepth_261_; lean_object* v_ref_262_; uint8_t v_suppressElabErrors_263_; uint8_t v_isRecordingDeps_264_; lean_object* v___y_265_; lean_object* v___y_272_; uint8_t v___y_273_; uint16_t v___y_274_; lean_object* v___y_297_; 
v_toCold_231_ = lean_ctor_get(v_a_228_, 0);
v_currRecDepth_232_ = lean_ctor_get(v_a_228_, 1);
v_ref_233_ = lean_ctor_get(v_a_228_, 2);
v_suppressElabErrors_234_ = lean_ctor_get_uint8(v_a_228_, sizeof(void*)*3 + 2);
v_isRecordingDeps_235_ = lean_ctor_get_uint8(v_a_228_, sizeof(void*)*3 + 3);
v_fileName_236_ = lean_ctor_get(v_toCold_231_, 0);
v_fileMap_237_ = lean_ctor_get(v_toCold_231_, 1);
v_options_238_ = lean_ctor_get(v_toCold_231_, 2);
v_currNamespace_239_ = lean_ctor_get(v_toCold_231_, 4);
v_openDecls_240_ = lean_ctor_get(v_toCold_231_, 5);
v_initHeartbeats_241_ = lean_ctor_get(v_toCold_231_, 6);
v_maxHeartbeats_242_ = lean_ctor_get(v_toCold_231_, 7);
v_quotContext_243_ = lean_ctor_get(v_toCold_231_, 8);
v_currMacroScope_244_ = lean_ctor_get(v_toCold_231_, 9);
v_cancelTk_x3f_245_ = lean_ctor_get(v_toCold_231_, 10);
v_inheritedTraceOptions_246_ = lean_ctor_get(v_toCold_231_, 11);
v___x_247_ = lean_box(1);
if (v_isRecordingDeps_235_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Lean_pp_mvars_anonymous;
lean_inc_ref(v_options_238_);
v___x_309_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_238_, v___x_308_, v_isRecordingDeps_235_);
v___y_297_ = v___x_309_;
goto v___jp_296_;
}
else
{
lean_object* v___x_310_; 
lean_inc_ref(v_options_238_);
v___x_310_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_238_);
v___y_297_ = v___x_310_;
goto v___jp_296_;
}
v___jp_248_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_266_ = l_Lean_maxRecDepth;
v___x_267_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v___y_249_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_268_, 0, v_fileName_251_);
lean_ctor_set(v___x_268_, 1, v_fileMap_252_);
lean_ctor_set(v___x_268_, 2, v___y_249_);
lean_ctor_set(v___x_268_, 3, v___x_267_);
lean_ctor_set(v___x_268_, 4, v_currNamespace_253_);
lean_ctor_set(v___x_268_, 5, v_openDecls_254_);
lean_ctor_set(v___x_268_, 6, v_initHeartbeats_255_);
lean_ctor_set(v___x_268_, 7, v_maxHeartbeats_256_);
lean_ctor_set(v___x_268_, 8, v_quotContext_257_);
lean_ctor_set(v___x_268_, 9, v_currMacroScope_258_);
lean_ctor_set(v___x_268_, 10, v_cancelTk_x3f_259_);
lean_ctor_set(v___x_268_, 11, v_inheritedTraceOptions_260_);
lean_inc(v_ref_262_);
lean_inc(v_currRecDepth_261_);
v___x_269_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_currRecDepth_261_);
lean_ctor_set(v___x_269_, 2, v_ref_262_);
lean_ctor_set_uint16(v___x_269_, sizeof(void*)*3, v___y_250_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*3 + 2, v_suppressElabErrors_263_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*3 + 3, v_isRecordingDeps_264_);
v___x_270_ = l_Lean_PrettyPrinter_delab(v_e_225_, v___x_247_, v_a_226_, v_a_227_, v___x_269_, v___y_265_);
lean_dec_ref_known(v___x_269_, 3);
return v___x_270_;
}
v___jp_271_:
{
lean_object* v___x_275_; lean_object* v_env_276_; lean_object* v_nextMacroScope_277_; lean_object* v_ngen_278_; lean_object* v_auxDeclNGen_279_; lean_object* v_traceState_280_; lean_object* v_recordedDeps_281_; lean_object* v_messages_282_; lean_object* v_infoState_283_; lean_object* v_snapshotTasks_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_294_; 
v___x_275_ = lean_st_ref_take(v_a_229_);
v_env_276_ = lean_ctor_get(v___x_275_, 0);
v_nextMacroScope_277_ = lean_ctor_get(v___x_275_, 1);
v_ngen_278_ = lean_ctor_get(v___x_275_, 2);
v_auxDeclNGen_279_ = lean_ctor_get(v___x_275_, 3);
v_traceState_280_ = lean_ctor_get(v___x_275_, 4);
v_recordedDeps_281_ = lean_ctor_get(v___x_275_, 6);
v_messages_282_ = lean_ctor_get(v___x_275_, 7);
v_infoState_283_ = lean_ctor_get(v___x_275_, 8);
v_snapshotTasks_284_ = lean_ctor_get(v___x_275_, 9);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_275_, 5);
lean_dec(v_unused_295_);
v___x_286_ = v___x_275_;
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_snapshotTasks_284_);
lean_inc(v_infoState_283_);
lean_inc(v_messages_282_);
lean_inc(v_recordedDeps_281_);
lean_inc(v_traceState_280_);
lean_inc(v_auxDeclNGen_279_);
lean_inc(v_ngen_278_);
lean_inc(v_nextMacroScope_277_);
lean_inc(v_env_276_);
lean_dec(v___x_275_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_288_ = l_Lean_Kernel_enableDiag(v_env_276_, v___y_273_);
v___x_289_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 5, v___x_289_);
lean_ctor_set(v___x_286_, 0, v___x_288_);
v___x_291_ = v___x_286_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_nextMacroScope_277_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_ngen_278_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_auxDeclNGen_279_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_traceState_280_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_293_, 6, v_recordedDeps_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 7, v_messages_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 8, v_infoState_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 9, v_snapshotTasks_284_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_st_ref_put(v_a_229_, v___x_291_);
lean_inc_ref(v_inheritedTraceOptions_246_);
lean_inc(v_cancelTk_x3f_245_);
lean_inc(v_currMacroScope_244_);
lean_inc(v_quotContext_243_);
lean_inc(v_maxHeartbeats_242_);
lean_inc(v_initHeartbeats_241_);
lean_inc(v_openDecls_240_);
lean_inc(v_currNamespace_239_);
lean_inc_ref(v_fileMap_237_);
lean_inc_ref(v_fileName_236_);
v___y_249_ = v___y_272_;
v___y_250_ = v___y_274_;
v_fileName_251_ = v_fileName_236_;
v_fileMap_252_ = v_fileMap_237_;
v_currNamespace_253_ = v_currNamespace_239_;
v_openDecls_254_ = v_openDecls_240_;
v_initHeartbeats_255_ = v_initHeartbeats_241_;
v_maxHeartbeats_256_ = v_maxHeartbeats_242_;
v_quotContext_257_ = v_quotContext_243_;
v_currMacroScope_258_ = v_currMacroScope_244_;
v_cancelTk_x3f_259_ = v_cancelTk_x3f_245_;
v_inheritedTraceOptions_260_ = v_inheritedTraceOptions_246_;
v_currRecDepth_261_ = v_currRecDepth_232_;
v_ref_262_ = v_ref_233_;
v_suppressElabErrors_263_ = v_suppressElabErrors_234_;
v_isRecordingDeps_264_ = v_isRecordingDeps_235_;
v___y_265_ = v_a_229_;
goto v___jp_248_;
}
}
}
v___jp_296_:
{
uint16_t v___x_298_; lean_object* v___x_299_; lean_object* v_env_300_; uint8_t v___x_301_; uint16_t v___x_302_; uint16_t v___x_303_; uint16_t v___x_304_; uint8_t v___x_305_; 
v___x_298_ = l_Lean_OptionFlags_ofOptions(v___y_297_);
v___x_299_ = lean_st_ref_get(v_a_229_);
v_env_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc_ref(v_env_300_);
lean_dec(v___x_299_);
v___x_301_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_300_);
lean_dec_ref(v_env_300_);
v___x_302_ = 512;
v___x_303_ = lean_uint16_land(v___x_298_, v___x_302_);
v___x_304_ = 0;
v___x_305_ = lean_uint16_dec_eq(v___x_303_, v___x_304_);
if (v___x_305_ == 0)
{
if (v___x_301_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = 1;
v___y_272_ = v___y_297_;
v___y_273_ = v___x_306_;
v___y_274_ = v___x_298_;
goto v___jp_271_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_246_);
lean_inc(v_cancelTk_x3f_245_);
lean_inc(v_currMacroScope_244_);
lean_inc(v_quotContext_243_);
lean_inc(v_maxHeartbeats_242_);
lean_inc(v_initHeartbeats_241_);
lean_inc(v_openDecls_240_);
lean_inc(v_currNamespace_239_);
lean_inc_ref(v_fileMap_237_);
lean_inc_ref(v_fileName_236_);
v___y_249_ = v___y_297_;
v___y_250_ = v___x_298_;
v_fileName_251_ = v_fileName_236_;
v_fileMap_252_ = v_fileMap_237_;
v_currNamespace_253_ = v_currNamespace_239_;
v_openDecls_254_ = v_openDecls_240_;
v_initHeartbeats_255_ = v_initHeartbeats_241_;
v_maxHeartbeats_256_ = v_maxHeartbeats_242_;
v_quotContext_257_ = v_quotContext_243_;
v_currMacroScope_258_ = v_currMacroScope_244_;
v_cancelTk_x3f_259_ = v_cancelTk_x3f_245_;
v_inheritedTraceOptions_260_ = v_inheritedTraceOptions_246_;
v_currRecDepth_261_ = v_currRecDepth_232_;
v_ref_262_ = v_ref_233_;
v_suppressElabErrors_263_ = v_suppressElabErrors_234_;
v_isRecordingDeps_264_ = v_isRecordingDeps_235_;
v___y_265_ = v_a_229_;
goto v___jp_248_;
}
}
else
{
if (v___x_301_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_246_);
lean_inc(v_cancelTk_x3f_245_);
lean_inc(v_currMacroScope_244_);
lean_inc(v_quotContext_243_);
lean_inc(v_maxHeartbeats_242_);
lean_inc(v_initHeartbeats_241_);
lean_inc(v_openDecls_240_);
lean_inc(v_currNamespace_239_);
lean_inc_ref(v_fileMap_237_);
lean_inc_ref(v_fileName_236_);
v___y_249_ = v___y_297_;
v___y_250_ = v___x_298_;
v_fileName_251_ = v_fileName_236_;
v_fileMap_252_ = v_fileMap_237_;
v_currNamespace_253_ = v_currNamespace_239_;
v_openDecls_254_ = v_openDecls_240_;
v_initHeartbeats_255_ = v_initHeartbeats_241_;
v_maxHeartbeats_256_ = v_maxHeartbeats_242_;
v_quotContext_257_ = v_quotContext_243_;
v_currMacroScope_258_ = v_currMacroScope_244_;
v_cancelTk_x3f_259_ = v_cancelTk_x3f_245_;
v_inheritedTraceOptions_260_ = v_inheritedTraceOptions_246_;
v_currRecDepth_261_ = v_currRecDepth_232_;
v_ref_262_ = v_ref_233_;
v_suppressElabErrors_263_ = v_suppressElabErrors_234_;
v_isRecordingDeps_264_ = v_isRecordingDeps_235_;
v___y_265_ = v_a_229_;
goto v___jp_248_;
}
else
{
uint8_t v___x_307_; 
v___x_307_ = 0;
v___y_272_ = v___y_297_;
v___y_273_ = v___x_307_;
v___y_274_ = v___x_298_;
goto v___jp_271_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_225_ = stack[0].m_obj;
lean_object* v_a_226_ = stack[1].m_obj;
lean_object* v_a_227_ = stack[2].m_obj;
lean_object* v_a_228_ = stack[3].m_obj;
lean_object* v_a_229_ = stack[4].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___boxed(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
return v_res_318_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; uint8_t v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; lean_object* v_toCold_330_; lean_object* v_mctx_331_; lean_object* v_lctx_332_; lean_object* v_options_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = 0;
v_env_328_ = l_Lean_Environment_setRecordingDeps(v_env_326_, v___x_327_);
v___x_329_ = lean_st_ref_get(v___y_321_);
v_toCold_330_ = lean_ctor_get(v___y_322_, 0);
v_mctx_331_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_331_);
lean_dec(v___x_329_);
v_lctx_332_ = lean_ctor_get(v___y_320_, 2);
v_options_333_ = lean_ctor_get(v_toCold_330_, 2);
lean_inc_ref(v_options_333_);
lean_inc_ref(v_lctx_332_);
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v_env_328_);
lean_ctor_set(v___x_334_, 1, v_mctx_331_);
lean_ctor_set(v___x_334_, 2, v_lctx_332_);
lean_ctor_set(v___x_334_, 3, v_options_333_);
v___x_335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_msgData_319_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_319_ = stack[0].m_obj;
lean_object* v___y_320_ = stack[1].m_obj;
lean_object* v___y_321_ = stack[2].m_obj;
lean_object* v___y_322_ = stack[3].m_obj;
lean_object* v___y_323_ = stack[4].m_obj;
lean_object* v_res_337_;
v_res_337_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msgData_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0___boxed(lean_object* v_msgData_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msgData_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object* v_e_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
lean_inc_ref(v_e_348_);
v___x_354_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_370_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = l_Lean_MessageData_ofExpr(v_e_348_);
v___x_357_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_356_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_370_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_362_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1));
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_a_355_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_a_358_);
v___x_366_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_364_);
lean_ctor_set(v___x_366_, 3, v___x_364_);
lean_ctor_set(v___x_366_, 4, v___x_365_);
lean_ctor_set(v___x_366_, 5, v___x_364_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_366_);
v___x_368_ = v___x_360_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_e_348_);
v_a_371_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_354_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_354_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_348_ = stack[0].m_obj;
lean_object* v_a_349_ = stack[1].m_obj;
lean_object* v_a_350_ = stack[2].m_obj;
lean_object* v_a_351_ = stack[3].m_obj;
lean_object* v_a_352_ = stack[4].m_obj;
lean_object* v_res_379_;
v_res_379_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___boxed(lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_390_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_ctor_set(v___x_392_, 3, v___x_391_);
lean_ctor_set(v___x_392_, 4, v___x_390_);
lean_ctor_set(v___x_392_, 5, v___x_390_);
lean_ctor_set(v___x_392_, 6, v___x_390_);
lean_ctor_set(v___x_392_, 7, v___x_390_);
lean_ctor_set(v___x_392_, 8, v___x_390_);
lean_ctor_set(v___x_392_, 9, v___x_390_);
lean_ctor_set(v___x_392_, 10, v___x_390_);
lean_ctor_set(v___x_392_, 11, v___x_389_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(32u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_unsigned_to_nat(32u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2);
v___x_401_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_397_);
lean_ctor_set(v___x_401_, 3, v___x_397_);
lean_ctor_set_usize(v___x_401_, 4, v___x_396_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_box(1);
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3);
v___x_404_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(lean_object* v_msgData_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_toCold_411_; lean_object* v_env_412_; lean_object* v_options_413_; uint8_t v___x_414_; lean_object* v_env_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_410_ = lean_st_ref_get(v___y_408_);
v_toCold_411_ = lean_ctor_get(v___y_407_, 0);
v_env_412_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_env_412_);
lean_dec(v___x_410_);
v_options_413_ = lean_ctor_get(v_toCold_411_, 2);
v___x_414_ = 0;
v_env_415_ = l_Lean_Environment_setRecordingDeps(v_env_412_, v___x_414_);
v___x_416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
v___x_417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4);
lean_inc_ref(v_options_413_);
v___x_418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_418_, 0, v_env_415_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___x_417_);
lean_ctor_set(v___x_418_, 3, v_options_413_);
v___x_419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v_msgData_406_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_406_ = stack[0].m_obj;
lean_object* v___y_407_ = stack[1].m_obj;
lean_object* v___y_408_ = stack[2].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msgData_406_, v___y_407_, v___y_408_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msgData_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_426_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(lean_object* v_opts_427_, lean_object* v_opt_428_){
_start:
{
lean_object* v_name_429_; lean_object* v_defValue_430_; lean_object* v_map_431_; lean_object* v___x_432_; 
v_name_429_ = lean_ctor_get(v_opt_428_, 0);
v_defValue_430_ = lean_ctor_get(v_opt_428_, 1);
v_map_431_ = lean_ctor_get(v_opts_427_, 0);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_431_, v_name_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = lean_unbox(v_defValue_430_);
return v___x_433_;
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_432_, 1);
if (lean_obj_tag(v_val_434_) == 1)
{
uint8_t v_v_435_; 
v_v_435_ = lean_ctor_get_uint8(v_val_434_, 0);
lean_dec_ref_known(v_val_434_, 0);
return v_v_435_;
}
else
{
uint8_t v___x_436_; 
lean_dec(v_val_434_);
v___x_436_ = lean_unbox(v_defValue_430_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_427_ = stack[0].m_obj;
lean_object* v_opt_428_ = stack[1].m_obj;
uint8_t v_res_437_;
v_res_437_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v_opts_427_, v_opt_428_);
stack->m_num = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_438_, lean_object* v_opt_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v_opts_438_, v_opt_439_);
lean_dec_ref(v_opt_439_);
lean_dec_ref(v_opts_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_448_, uint8_t v___y_449_, lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 1)
{
lean_object* v_pre_451_; 
v_pre_451_ = lean_ctor_get(v_x_450_, 0);
switch(lean_obj_tag(v_pre_451_))
{
case 1:
{
lean_object* v_pre_452_; 
v_pre_452_ = lean_ctor_get(v_pre_451_, 0);
switch(lean_obj_tag(v_pre_452_))
{
case 0:
{
lean_object* v_str_453_; lean_object* v_str_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_str_453_ = lean_ctor_get(v_x_450_, 1);
v_str_454_ = lean_ctor_get(v_pre_451_, 1);
v___x_455_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0));
v___x_456_ = lean_string_dec_eq(v_str_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4));
v___x_458_ = lean_string_dec_eq(v_str_454_, v___x_457_);
if (v___x_458_ == 0)
{
return v___x_458_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1));
v___x_460_ = lean_string_dec_eq(v_str_453_, v___x_459_);
if (v___x_460_ == 0)
{
return v___x_460_;
}
else
{
return v_suppressElabErrors_448_;
}
}
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2));
v___x_462_ = lean_string_dec_eq(v_str_453_, v___x_461_);
if (v___x_462_ == 0)
{
return v___x_462_;
}
else
{
return v_suppressElabErrors_448_;
}
}
}
case 1:
{
lean_object* v_pre_463_; 
v_pre_463_ = lean_ctor_get(v_pre_452_, 0);
if (lean_obj_tag(v_pre_463_) == 0)
{
lean_object* v_str_464_; lean_object* v_str_465_; lean_object* v_str_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_str_464_ = lean_ctor_get(v_x_450_, 1);
v_str_465_ = lean_ctor_get(v_pre_451_, 1);
v_str_466_ = lean_ctor_get(v_pre_452_, 1);
v___x_467_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3));
v___x_468_ = lean_string_dec_eq(v_str_466_, v___x_467_);
if (v___x_468_ == 0)
{
return v___x_468_;
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4));
v___x_470_ = lean_string_dec_eq(v_str_465_, v___x_469_);
if (v___x_470_ == 0)
{
return v___x_470_;
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5));
v___x_472_ = lean_string_dec_eq(v_str_464_, v___x_471_);
if (v___x_472_ == 0)
{
return v___x_472_;
}
else
{
return v_suppressElabErrors_448_;
}
}
}
}
else
{
return v___y_449_;
}
}
default: 
{
return v___y_449_;
}
}
}
case 0:
{
lean_object* v_str_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_str_473_ = lean_ctor_get(v_x_450_, 1);
v___x_474_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__0));
v___x_475_ = lean_string_dec_eq(v_str_473_, v___x_474_);
if (v___x_475_ == 0)
{
return v___x_475_;
}
else
{
return v_suppressElabErrors_448_;
}
}
default: 
{
return v___y_449_;
}
}
}
else
{
return v___y_449_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_448_ = stack[0].m_num;
uint8_t v___y_449_ = stack[1].m_num;
lean_object* v_x_450_ = stack[2].m_obj;
uint8_t v_res_476_;
v_res_476_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v_suppressElabErrors_448_, v___y_449_, v_x_450_);
stack->m_num = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_477_, lean_object* v___y_478_, lean_object* v_x_479_){
_start:
{
uint8_t v_suppressElabErrors_boxed_480_; uint8_t v___y_2811__boxed_481_; uint8_t v_res_482_; lean_object* v_r_483_; 
v_suppressElabErrors_boxed_480_ = lean_unbox(v_suppressElabErrors_477_);
v___y_2811__boxed_481_ = lean_unbox(v___y_478_);
v_res_482_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_480_, v___y_2811__boxed_481_, v_x_479_);
lean_dec(v_x_479_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(lean_object* v_ref_485_, lean_object* v_msgData_486_, uint8_t v_severity_487_, uint8_t v_isSilent_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___y_493_; uint8_t v___y_494_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_toCold_500_; lean_object* v___y_501_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; uint8_t v___y_533_; uint8_t v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; uint8_t v___y_562_; lean_object* v___y_563_; uint8_t v___y_567_; uint8_t v___y_568_; uint8_t v___y_569_; uint8_t v___x_580_; uint8_t v___y_582_; uint8_t v___y_583_; uint8_t v___y_584_; uint8_t v___y_586_; uint8_t v___x_594_; 
v___x_580_ = 2;
v___x_594_ = l_Lean_instBEqMessageSeverity_beq(v_severity_487_, v___x_580_);
if (v___x_594_ == 0)
{
v___y_586_ = v___x_594_;
goto v___jp_585_;
}
else
{
uint8_t v___x_595_; 
lean_inc_ref(v_msgData_486_);
v___x_595_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_486_);
v___y_586_ = v___x_595_;
goto v___jp_585_;
}
v___jp_492_:
{
lean_object* v_currNamespace_502_; lean_object* v_openDecls_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_env_508_; lean_object* v_nextMacroScope_509_; lean_object* v_ngen_510_; lean_object* v_auxDeclNGen_511_; lean_object* v_traceState_512_; lean_object* v_cache_513_; lean_object* v_recordedDeps_514_; lean_object* v_messages_515_; lean_object* v_infoState_516_; lean_object* v_snapshotTasks_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_528_; 
v_currNamespace_502_ = lean_ctor_get(v_toCold_500_, 4);
v_openDecls_503_ = lean_ctor_get(v_toCold_500_, 5);
lean_inc(v_openDecls_503_);
lean_inc(v_currNamespace_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_currNamespace_502_);
lean_ctor_set(v___x_504_, 1, v_openDecls_503_);
v___x_505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc_ref(v___y_493_);
v___x_506_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_506_, 0, v___y_493_);
lean_ctor_set(v___x_506_, 1, v___y_495_);
lean_ctor_set(v___x_506_, 2, v___y_499_);
lean_ctor_set(v___x_506_, 3, v___y_497_);
lean_ctor_set(v___x_506_, 4, v___x_505_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*5, v___y_494_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*5 + 1, v___y_496_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*5 + 2, v_isSilent_488_);
v___x_507_ = lean_st_ref_take(v___y_501_);
v_env_508_ = lean_ctor_get(v___x_507_, 0);
v_nextMacroScope_509_ = lean_ctor_get(v___x_507_, 1);
v_ngen_510_ = lean_ctor_get(v___x_507_, 2);
v_auxDeclNGen_511_ = lean_ctor_get(v___x_507_, 3);
v_traceState_512_ = lean_ctor_get(v___x_507_, 4);
v_cache_513_ = lean_ctor_get(v___x_507_, 5);
v_recordedDeps_514_ = lean_ctor_get(v___x_507_, 6);
v_messages_515_ = lean_ctor_get(v___x_507_, 7);
v_infoState_516_ = lean_ctor_get(v___x_507_, 8);
v_snapshotTasks_517_ = lean_ctor_get(v___x_507_, 9);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_528_ == 0)
{
v___x_519_ = v___x_507_;
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snapshotTasks_517_);
lean_inc(v_infoState_516_);
lean_inc(v_messages_515_);
lean_inc(v_recordedDeps_514_);
lean_inc(v_cache_513_);
lean_inc(v_traceState_512_);
lean_inc(v_auxDeclNGen_511_);
lean_inc(v_ngen_510_);
lean_inc(v_nextMacroScope_509_);
lean_inc(v_env_508_);
lean_dec(v___x_507_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_521_ = lean_box(0);
v___x_522_ = l_Lean_MessageLog_add(v___x_506_, v_messages_515_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 7, v___x_522_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_env_508_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_nextMacroScope_509_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_ngen_510_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_auxDeclNGen_511_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_traceState_512_);
lean_ctor_set(v_reuseFailAlloc_527_, 5, v_cache_513_);
lean_ctor_set(v_reuseFailAlloc_527_, 6, v_recordedDeps_514_);
lean_ctor_set(v_reuseFailAlloc_527_, 7, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_527_, 8, v_infoState_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 9, v_snapshotTasks_517_);
v___x_524_ = v_reuseFailAlloc_527_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_st_ref_put(v___y_501_, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_521_);
return v___x_526_;
}
}
}
v___jp_529_:
{
lean_object* v_fileName_538_; lean_object* v_fileMap_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_555_; 
v_fileName_538_ = lean_ctor_get(v___y_536_, 0);
v_fileMap_539_ = lean_ctor_get(v___y_536_, 1);
v___x_540_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_486_);
v___x_541_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v___x_540_, v___y_489_, v___y_490_);
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_555_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_inc_ref_n(v_fileMap_539_, 2);
v___x_546_ = l_Lean_FileMap_toPosition(v_fileMap_539_, v___y_535_);
lean_dec(v___y_535_);
v___x_547_ = l_Lean_FileMap_toPosition(v_fileMap_539_, v___y_537_);
lean_dec(v___y_537_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_534_ == 0)
{
lean_del_object(v___x_544_);
lean_dec_ref(v___y_530_);
v___y_493_ = v_fileName_538_;
v___y_494_ = v___y_532_;
v___y_495_ = v___x_546_;
v___y_496_ = v___y_533_;
v___y_497_ = v___x_549_;
v___y_498_ = v_a_542_;
v___y_499_ = v___x_548_;
v_toCold_500_ = v___y_531_;
v___y_501_ = v___y_490_;
goto v___jp_492_;
}
else
{
uint8_t v___x_550_; 
lean_inc(v_a_542_);
v___x_550_ = l_Lean_MessageData_hasTag(v___y_530_, v_a_542_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec_ref_known(v___x_548_, 1);
lean_dec_ref(v___x_546_);
lean_dec(v_a_542_);
v___x_551_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_551_);
v___x_553_ = v___x_544_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_del_object(v___x_544_);
v___y_493_ = v_fileName_538_;
v___y_494_ = v___y_532_;
v___y_495_ = v___x_546_;
v___y_496_ = v___y_533_;
v___y_497_ = v___x_549_;
v___y_498_ = v_a_542_;
v___y_499_ = v___x_548_;
v_toCold_500_ = v___y_531_;
v___y_501_ = v___y_490_;
goto v___jp_492_;
}
}
}
}
v___jp_556_:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Syntax_getTailPos_x3f(v___y_561_, v___y_560_);
lean_dec(v___y_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_inc(v___y_563_);
v___y_530_ = v___y_558_;
v___y_531_ = v___y_559_;
v___y_532_ = v___y_560_;
v___y_533_ = v___y_562_;
v___y_534_ = v___y_557_;
v___y_535_ = v___y_563_;
v___y_536_ = v___y_559_;
v___y_537_ = v___y_563_;
goto v___jp_529_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v___x_564_, 1);
v___y_530_ = v___y_558_;
v___y_531_ = v___y_559_;
v___y_532_ = v___y_560_;
v___y_533_ = v___y_562_;
v___y_534_ = v___y_557_;
v___y_535_ = v___y_563_;
v___y_536_ = v___y_559_;
v___y_537_ = v_val_565_;
goto v___jp_529_;
}
}
v___jp_566_:
{
lean_object* v_toCold_570_; lean_object* v_ref_571_; uint8_t v_suppressElabErrors_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___f_575_; lean_object* v_ref_576_; lean_object* v___x_577_; 
v_toCold_570_ = lean_ctor_get(v___y_489_, 0);
v_ref_571_ = lean_ctor_get(v___y_489_, 2);
v_suppressElabErrors_572_ = lean_ctor_get_uint8(v___y_489_, sizeof(void*)*3 + 2);
v___x_573_ = lean_box(v_suppressElabErrors_572_);
v___x_574_ = lean_box(v___y_567_);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_575_, 0, v___x_573_);
lean_closure_set(v___f_575_, 1, v___x_574_);
v_ref_576_ = l_Lean_replaceRef(v_ref_485_, v_ref_571_);
v___x_577_ = l_Lean_Syntax_getPos_x3f(v_ref_576_, v___y_568_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___y_557_ = v_suppressElabErrors_572_;
v___y_558_ = v___f_575_;
v___y_559_ = v_toCold_570_;
v___y_560_ = v___y_568_;
v___y_561_ = v_ref_576_;
v___y_562_ = v___y_569_;
v___y_563_ = v___x_578_;
goto v___jp_556_;
}
else
{
lean_object* v_val_579_; 
v_val_579_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_577_, 1);
v___y_557_ = v_suppressElabErrors_572_;
v___y_558_ = v___f_575_;
v___y_559_ = v_toCold_570_;
v___y_560_ = v___y_568_;
v___y_561_ = v_ref_576_;
v___y_562_ = v___y_569_;
v___y_563_ = v_val_579_;
goto v___jp_556_;
}
}
v___jp_581_:
{
if (v___y_584_ == 0)
{
v___y_567_ = v___y_582_;
v___y_568_ = v___y_583_;
v___y_569_ = v_severity_487_;
goto v___jp_566_;
}
else
{
v___y_567_ = v___y_582_;
v___y_568_ = v___y_583_;
v___y_569_ = v___x_580_;
goto v___jp_566_;
}
}
v___jp_585_:
{
if (v___y_586_ == 0)
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 1;
v___x_588_ = l_Lean_instBEqMessageSeverity_beq(v_severity_487_, v___x_587_);
if (v___x_588_ == 0)
{
v___y_582_ = v___y_586_;
v___y_583_ = v___y_586_;
v___y_584_ = v___x_588_;
goto v___jp_581_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_489_);
v___x_590_ = l_Lean_warningAsError;
v___x_591_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v___x_589_, v___x_590_);
lean_dec_ref(v___x_589_);
v___y_582_ = v___y_586_;
v___y_583_ = v___y_586_;
v___y_584_ = v___x_591_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec_ref(v_msgData_486_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_485_ = stack[0].m_obj;
lean_object* v_msgData_486_ = stack[1].m_obj;
uint8_t v_severity_487_ = stack[2].m_num;
uint8_t v_isSilent_488_ = stack[3].m_num;
lean_object* v___y_489_ = stack[4].m_obj;
lean_object* v___y_490_ = stack[5].m_obj;
lean_object* v_res_596_;
v_res_596_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_485_, v_msgData_486_, v_severity_487_, v_isSilent_488_, v___y_489_, v___y_490_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___boxed(lean_object* v_ref_597_, lean_object* v_msgData_598_, lean_object* v_severity_599_, lean_object* v_isSilent_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
uint8_t v_severity_boxed_604_; uint8_t v_isSilent_boxed_605_; lean_object* v_res_606_; 
v_severity_boxed_604_ = lean_unbox(v_severity_599_);
v_isSilent_boxed_605_ = lean_unbox(v_isSilent_600_);
v_res_606_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_597_, v_msgData_598_, v_severity_boxed_604_, v_isSilent_boxed_605_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v_ref_597_);
return v_res_606_;
}
}
lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object* v_ref_607_, lean_object* v_msgData_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = 0;
v___x_613_ = 0;
v___x_614_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_607_, v_msgData_608_, v___x_612_, v___x_613_, v___y_609_, v___y_610_);
return v___x_614_;
}
}
LEAN_EXPORT void l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_607_ = stack[0].m_obj;
lean_object* v_msgData_608_ = stack[1].m_obj;
lean_object* v___y_609_ = stack[2].m_obj;
lean_object* v___y_610_ = stack[3].m_obj;
lean_object* v_res_615_;
v_res_615_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_607_, v_msgData_608_, v___y_609_, v___y_610_);
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object* v_ref_616_, lean_object* v_msgData_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_616_, v_msgData_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v_ref_616_);
return v_res_621_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* v_ref_622_, lean_object* v_s_623_, lean_object* v_origSpan_x3f_624_, lean_object* v_header_625_, lean_object* v_codeActionPrefix_x3f_626_, uint8_t v_diffGranularity_627_, lean_object* v_footer_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; lean_object* v_hintSuggestion_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___x_638_; 
v___x_632_ = lean_box(0);
v_hintSuggestion_633_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_hintSuggestion_633_, 0, v_s_623_);
lean_ctor_set(v_hintSuggestion_633_, 1, v_origSpan_x3f_624_);
lean_ctor_set(v_hintSuggestion_633_, 2, v___x_632_);
lean_ctor_set_uint8(v_hintSuggestion_633_, sizeof(void*)*3, v_diffGranularity_627_);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_mk_empty_array_with_capacity(v___x_634_);
v___x_636_ = lean_array_push(v___x_635_, v_hintSuggestion_633_);
v___x_637_ = 0;
lean_inc(v_ref_622_);
v___x_638_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v___x_636_, v_ref_622_, v_codeActionPrefix_x3f_626_, v___x_637_, v_a_629_, v_a_630_);
lean_dec_ref(v___x_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l_Lean_stringToMessageData(v_header_625_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_a_639_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v_footer_628_);
v___x_643_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_622_, v___x_642_, v_a_629_, v_a_630_);
lean_dec(v_ref_622_);
return v___x_643_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v_footer_628_);
lean_dec_ref(v_header_625_);
lean_dec(v_ref_622_);
v_a_644_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_638_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_638_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_622_ = stack[0].m_obj;
lean_object* v_s_623_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_624_ = stack[2].m_obj;
lean_object* v_header_625_ = stack[3].m_obj;
lean_object* v_codeActionPrefix_x3f_626_ = stack[4].m_obj;
uint8_t v_diffGranularity_627_ = stack[5].m_num;
lean_object* v_footer_628_ = stack[6].m_obj;
lean_object* v_a_629_ = stack[7].m_obj;
lean_object* v_a_630_ = stack[8].m_obj;
lean_object* v_res_652_;
v_res_652_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_622_, v_s_623_, v_origSpan_x3f_624_, v_header_625_, v_codeActionPrefix_x3f_626_, v_diffGranularity_627_, v_footer_628_, v_a_629_, v_a_630_);
stack->m_obj
 = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* v_ref_653_, lean_object* v_s_654_, lean_object* v_origSpan_x3f_655_, lean_object* v_header_656_, lean_object* v_codeActionPrefix_x3f_657_, lean_object* v_diffGranularity_658_, lean_object* v_footer_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
uint8_t v_diffGranularity_boxed_663_; lean_object* v_res_664_; 
v_diffGranularity_boxed_663_ = lean_unbox(v_diffGranularity_658_);
v_res_664_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_653_, v_s_654_, v_origSpan_x3f_655_, v_header_656_, v_codeActionPrefix_x3f_657_, v_diffGranularity_boxed_663_, v_footer_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_664_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_ref_669_ = lean_ctor_get(v___y_666_, 2);
v___x_670_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msg_665_, v___y_666_, v___y_667_);
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_ref_669_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_ref_669_);
lean_ctor_set(v___x_675_, 1, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_665_ = stack[0].m_obj;
lean_object* v___y_666_ = stack[1].m_obj;
lean_object* v___y_667_ = stack[2].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_665_, v___y_666_, v___y_667_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_685_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(lean_object* v_ref_686_, lean_object* v_msg_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_toCold_691_; lean_object* v_currRecDepth_692_; lean_object* v_ref_693_; uint16_t v_optionFlags_694_; uint8_t v_suppressElabErrors_695_; uint8_t v_isRecordingDeps_696_; lean_object* v_ref_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_toCold_691_ = lean_ctor_get(v___y_688_, 0);
v_currRecDepth_692_ = lean_ctor_get(v___y_688_, 1);
v_ref_693_ = lean_ctor_get(v___y_688_, 2);
v_optionFlags_694_ = lean_ctor_get_uint16(v___y_688_, sizeof(void*)*3);
v_suppressElabErrors_695_ = lean_ctor_get_uint8(v___y_688_, sizeof(void*)*3 + 2);
v_isRecordingDeps_696_ = lean_ctor_get_uint8(v___y_688_, sizeof(void*)*3 + 3);
v_ref_697_ = l_Lean_replaceRef(v_ref_686_, v_ref_693_);
lean_inc(v_currRecDepth_692_);
lean_inc_ref(v_toCold_691_);
v___x_698_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_698_, 0, v_toCold_691_);
lean_ctor_set(v___x_698_, 1, v_currRecDepth_692_);
lean_ctor_set(v___x_698_, 2, v_ref_697_);
lean_ctor_set_uint16(v___x_698_, sizeof(void*)*3, v_optionFlags_694_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*3 + 2, v_suppressElabErrors_695_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*3 + 3, v_isRecordingDeps_696_);
v___x_699_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_687_, v___x_698_, v___y_689_);
lean_dec_ref_known(v___x_698_, 3);
return v___x_699_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_686_ = stack[0].m_obj;
lean_object* v_msg_687_ = stack[1].m_obj;
lean_object* v___y_688_ = stack[2].m_obj;
lean_object* v___y_689_ = stack[3].m_obj;
lean_object* v_res_700_;
v_res_700_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_686_, v_msg_687_, v___y_688_, v___y_689_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg___boxed(lean_object* v_ref_701_, lean_object* v_msg_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_701_, v_msg_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v_ref_701_);
return v_res_706_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(lean_object* v_origSpan_x3f_707_, uint8_t v_diffGranularity_708_, size_t v_sz_709_, size_t v_i_710_, lean_object* v_bs_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_lt(v_i_710_, v_sz_709_);
if (v___x_712_ == 0)
{
lean_dec(v_origSpan_x3f_707_);
return v_bs_711_;
}
else
{
lean_object* v_v_713_; lean_object* v___x_714_; lean_object* v_bs_x27_715_; lean_object* v___x_716_; lean_object* v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v_v_713_ = lean_array_uget(v_bs_711_, v_i_710_);
v___x_714_ = lean_unsigned_to_nat(0u);
v_bs_x27_715_ = lean_array_uset(v_bs_711_, v_i_710_, v___x_714_);
v___x_716_ = lean_box(0);
lean_inc(v_origSpan_x3f_707_);
v___x_717_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_717_, 0, v_v_713_);
lean_ctor_set(v___x_717_, 1, v_origSpan_x3f_707_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*3, v_diffGranularity_708_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_710_, v___x_718_);
v___x_720_ = lean_array_uset(v_bs_x27_715_, v_i_710_, v___x_717_);
v_i_710_ = v___x_719_;
v_bs_711_ = v___x_720_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_origSpan_x3f_707_ = stack[0].m_obj;
uint8_t v_diffGranularity_708_ = stack[1].m_num;
size_t v_sz_709_ = stack[2].m_num;
size_t v_i_710_ = stack[3].m_num;
lean_object* v_bs_711_ = stack[4].m_obj;
lean_object* v_res_722_;
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_707_, v_diffGranularity_708_, v_sz_709_, v_i_710_, v_bs_711_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object* v_origSpan_x3f_723_, lean_object* v_diffGranularity_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_bs_727_){
_start:
{
uint8_t v_diffGranularity_boxed_728_; size_t v_sz_boxed_729_; size_t v_i_boxed_730_; lean_object* v_res_731_; 
v_diffGranularity_boxed_728_ = lean_unbox(v_diffGranularity_724_);
v_sz_boxed_729_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_730_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_723_, v_diffGranularity_boxed_728_, v_sz_boxed_729_, v_i_boxed_730_, v_bs_727_);
return v_res_731_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object* v_ref_735_, lean_object* v_suggestions_736_, lean_object* v_origSpan_x3f_737_, lean_object* v_header_738_, lean_object* v_codeActionPrefix_x3f_739_, uint8_t v_diffGranularity_740_, lean_object* v_footer_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = lean_array_get_size(v_suggestions_736_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_nat_dec_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
v___y_746_ = v_a_742_;
v___y_747_ = v_a_743_;
goto v___jp_745_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref(v_footer_741_);
lean_dec(v_codeActionPrefix_x3f_739_);
lean_dec_ref(v_header_738_);
lean_dec(v_origSpan_x3f_737_);
lean_dec_ref(v_suggestions_736_);
v___x_769_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1, &l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1);
v___x_770_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_735_, v___x_769_, v_a_742_, v_a_743_);
lean_dec(v_ref_735_);
return v___x_770_;
}
v___jp_745_:
{
size_t v_sz_748_; size_t v___x_749_; lean_object* v_hintSuggestions_750_; uint8_t v___x_751_; lean_object* v___x_752_; 
v_sz_748_ = lean_array_size(v_suggestions_736_);
v___x_749_ = ((size_t)0ULL);
v_hintSuggestions_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_737_, v_diffGranularity_740_, v_sz_748_, v___x_749_, v_suggestions_736_);
v___x_751_ = 1;
lean_inc(v_ref_735_);
v___x_752_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_hintSuggestions_750_, v_ref_735_, v_codeActionPrefix_x3f_739_, v___x_751_, v___y_746_, v___y_747_);
lean_dec_ref(v_hintSuggestions_750_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = l_Lean_stringToMessageData(v_header_738_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_a_753_);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_footer_741_);
v___x_757_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_735_, v___x_756_, v___y_746_, v___y_747_);
lean_dec(v_ref_735_);
return v___x_757_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_footer_741_);
lean_dec_ref(v_header_738_);
lean_dec(v_ref_735_);
v_a_758_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_752_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_752_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_735_ = stack[0].m_obj;
lean_object* v_suggestions_736_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_737_ = stack[2].m_obj;
lean_object* v_header_738_ = stack[3].m_obj;
lean_object* v_codeActionPrefix_x3f_739_ = stack[4].m_obj;
uint8_t v_diffGranularity_740_ = stack[5].m_num;
lean_object* v_footer_741_ = stack[6].m_obj;
lean_object* v_a_742_ = stack[7].m_obj;
lean_object* v_a_743_ = stack[8].m_obj;
lean_object* v_res_771_;
v_res_771_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_735_, v_suggestions_736_, v_origSpan_x3f_737_, v_header_738_, v_codeActionPrefix_x3f_739_, v_diffGranularity_740_, v_footer_741_, v_a_742_, v_a_743_);
stack->m_obj
 = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(lean_object* v_ref_772_, lean_object* v_suggestions_773_, lean_object* v_origSpan_x3f_774_, lean_object* v_header_775_, lean_object* v_codeActionPrefix_x3f_776_, lean_object* v_diffGranularity_777_, lean_object* v_footer_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
uint8_t v_diffGranularity_boxed_782_; lean_object* v_res_783_; 
v_diffGranularity_boxed_782_ = lean_unbox(v_diffGranularity_777_);
v_res_783_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_772_, v_suggestions_773_, v_origSpan_x3f_774_, v_header_775_, v_codeActionPrefix_x3f_776_, v_diffGranularity_boxed_782_, v_footer_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_783_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object* v_ref_784_, lean_object* v_suggestions_785_, lean_object* v_origSpan_x3f_786_, lean_object* v_header_787_, lean_object* v_style_x3f_788_, lean_object* v_codeActionPrefix_x3f_789_, uint8_t v_diffGranularity_790_, lean_object* v_footer_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_784_, v_suggestions_785_, v_origSpan_x3f_786_, v_header_787_, v_codeActionPrefix_x3f_789_, v_diffGranularity_790_, v_footer_791_, v_a_792_, v_a_793_);
return v___x_795_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addSuggestions_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_784_ = stack[0].m_obj;
lean_object* v_suggestions_785_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_786_ = stack[2].m_obj;
lean_object* v_header_787_ = stack[3].m_obj;
lean_object* v_style_x3f_788_ = stack[4].m_obj;
lean_object* v_codeActionPrefix_x3f_789_ = stack[5].m_obj;
uint8_t v_diffGranularity_790_ = stack[6].m_num;
lean_object* v_footer_791_ = stack[7].m_obj;
lean_object* v_a_792_ = stack[8].m_obj;
lean_object* v_a_793_ = stack[9].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_Lean_Meta_Tactic_TryThis_addSuggestions(v_ref_784_, v_suggestions_785_, v_origSpan_x3f_786_, v_header_787_, v_style_x3f_788_, v_codeActionPrefix_x3f_789_, v_diffGranularity_790_, v_footer_791_, v_a_792_, v_a_793_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object* v_ref_797_, lean_object* v_suggestions_798_, lean_object* v_origSpan_x3f_799_, lean_object* v_header_800_, lean_object* v_style_x3f_801_, lean_object* v_codeActionPrefix_x3f_802_, lean_object* v_diffGranularity_803_, lean_object* v_footer_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_diffGranularity_boxed_808_; lean_object* v_res_809_; 
v_diffGranularity_boxed_808_ = lean_unbox(v_diffGranularity_803_);
v_res_809_ = l_Lean_Meta_Tactic_TryThis_addSuggestions(v_ref_797_, v_suggestions_798_, v_origSpan_x3f_799_, v_header_800_, v_style_x3f_801_, v_codeActionPrefix_x3f_802_, v_diffGranularity_boxed_808_, v_footer_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_style_x3f_801_);
return v_res_809_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object* v_00_u03b1_810_, lean_object* v_ref_811_, lean_object* v_msg_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_811_, v_msg_812_, v___y_813_, v___y_814_);
return v___x_816_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_811_ = stack[1].m_obj;
lean_object* v_msg_812_ = stack[2].m_obj;
lean_object* v___y_813_ = stack[3].m_obj;
lean_object* v___y_814_ = stack[4].m_obj;
lean_object* v_res_817_;
v_res_817_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_box(0), v_ref_811_, v_msg_812_, v___y_813_, v___y_814_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object* v_00_u03b1_818_, lean_object* v_ref_819_, lean_object* v_msg_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(v_00_u03b1_818_, v_ref_819_, v_msg_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v_ref_819_);
return v_res_824_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(lean_object* v_00_u03b1_825_, lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_826_ = stack[1].m_obj;
lean_object* v___y_827_ = stack[2].m_obj;
lean_object* v___y_828_ = stack[3].m_obj;
lean_object* v_res_831_;
v_res_831_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(lean_box(0), v_msg_826_, v___y_827_, v___y_828_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___boxed(lean_object* v_00_u03b1_832_, lean_object* v_msg_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(v_00_u03b1_832_, v_msg_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_837_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(lean_object* v_a_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
v___x_848_ = lean_apply_2(v_a_838_, v___y_839_, v___y_840_);
v___x_849_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_848_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_849_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_838_ = stack[0].m_obj;
lean_object* v___y_839_ = stack[1].m_obj;
lean_object* v___y_840_ = stack[2].m_obj;
lean_object* v___y_841_ = stack[3].m_obj;
lean_object* v___y_842_ = stack[4].m_obj;
lean_object* v___y_843_ = stack[5].m_obj;
lean_object* v___y_844_ = stack[6].m_obj;
lean_object* v___y_845_ = stack[7].m_obj;
lean_object* v___y_846_ = stack[8].m_obj;
lean_object* v_res_850_;
v_res_850_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg___boxed(lean_object* v_a_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_861_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(lean_object* v_00_u03b1_862_, lean_object* v_a_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_873_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_863_ = stack[1].m_obj;
lean_object* v___y_864_ = stack[2].m_obj;
lean_object* v___y_865_ = stack[3].m_obj;
lean_object* v___y_866_ = stack[4].m_obj;
lean_object* v___y_867_ = stack[5].m_obj;
lean_object* v___y_868_ = stack[6].m_obj;
lean_object* v___y_869_ = stack[7].m_obj;
lean_object* v___y_870_ = stack[8].m_obj;
lean_object* v___y_871_ = stack[9].m_obj;
lean_object* v_res_874_;
v_res_874_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(lean_box(0), v_a_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___boxed(lean_object* v_00_u03b1_875_, lean_object* v_a_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(v_00_u03b1_875_, v_a_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_886_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(lean_object* v_e_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_Expr_hasMVar(v_e_887_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_e_887_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v_mctx_893_; lean_object* v___x_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_897_; lean_object* v_cache_898_; lean_object* v_zetaDeltaFVarIds_899_; lean_object* v_postponed_900_; lean_object* v_diag_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_910_; 
v___x_892_ = lean_st_ref_get(v___y_888_);
v_mctx_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_mctx_893_);
lean_dec(v___x_892_);
v___x_894_ = l_Lean_instantiateMVarsCore(v_mctx_893_, v_e_887_);
v_fst_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_fst_895_);
v_snd_896_ = lean_ctor_get(v___x_894_, 1);
lean_inc(v_snd_896_);
lean_dec_ref(v___x_894_);
v___x_897_ = lean_st_ref_take(v___y_888_);
v_cache_898_ = lean_ctor_get(v___x_897_, 1);
v_zetaDeltaFVarIds_899_ = lean_ctor_get(v___x_897_, 2);
v_postponed_900_ = lean_ctor_get(v___x_897_, 3);
v_diag_901_ = lean_ctor_get(v___x_897_, 4);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_897_, 0);
lean_dec(v_unused_911_);
v___x_903_ = v___x_897_;
v_isShared_904_ = v_isSharedCheck_910_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_diag_901_);
lean_inc(v_postponed_900_);
lean_inc(v_zetaDeltaFVarIds_899_);
lean_inc(v_cache_898_);
lean_dec(v___x_897_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_910_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v_snd_896_);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_snd_896_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_cache_898_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_zetaDeltaFVarIds_899_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_postponed_900_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_diag_901_);
v___x_906_ = v_reuseFailAlloc_909_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_st_ref_put(v___y_888_, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_fst_895_);
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_887_ = stack[0].m_obj;
lean_object* v___y_888_ = stack[1].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_887_, v___y_888_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(lean_object* v_e_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_913_, v___y_914_);
lean_dec(v___y_914_);
return v_res_916_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(lean_object* v_e_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_917_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_917_ = stack[0].m_obj;
lean_object* v___y_918_ = stack[1].m_obj;
lean_object* v___y_919_ = stack[2].m_obj;
lean_object* v___y_920_ = stack[3].m_obj;
lean_object* v___y_921_ = stack[4].m_obj;
lean_object* v___y_922_ = stack[5].m_obj;
lean_object* v___y_923_ = stack[6].m_obj;
lean_object* v___y_924_ = stack[7].m_obj;
lean_object* v___y_925_ = stack[8].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(lean_object* v_e_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_939_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_ref_946_; lean_object* v___x_947_; lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_ref_946_ = lean_ctor_get(v___y_943_, 2);
v___x_947_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_956_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
lean_inc(v_ref_946_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_ref_946_);
lean_ctor_set(v___x_952_, 1, v_a_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 1);
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_940_ = stack[0].m_obj;
lean_object* v___y_941_ = stack[1].m_obj;
lean_object* v___y_942_ = stack[2].m_obj;
lean_object* v___y_943_ = stack[3].m_obj;
lean_object* v___y_944_ = stack[4].m_obj;
lean_object* v_res_957_;
v_res_957_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* v_initialState_968_, lean_object* v_tac_969_, lean_object* v_expectedType_x3f_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_972_, v_a_974_, v_a_976_, v_a_978_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; uint8_t v___x_982_; lean_object* v_a_984_; lean_object* v_a_995_; lean_object* v___y_1006_; lean_object* v___x_1009_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = 0;
v___x_1009_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_initialState_968_, v___x_982_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref_known(v___x_1009_, 1);
v___x_1010_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1010_, 0, v_tac_969_);
v___x_1011_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_1011_, 0, lean_box(0));
lean_closure_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v___x_1011_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_dec_ref_known(v___x_1012_, 1);
if (lean_obj_tag(v_expectedType_x3f_970_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1014_; 
v_val_1013_ = lean_ctor_get(v_expectedType_x3f_970_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_expectedType_x3f_970_, 1);
v___x_1014_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_972_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = l_Lean_MVarId_getType(v_a_1015_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; uint8_t v___x_1022_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_1017_, v_a_976_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_val_1013_, v_a_976_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = lean_expr_eqv(v_a_1019_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec(v_a_1019_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
v___x_1024_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v___x_1023_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
v___y_1006_ = v___x_1024_;
goto v___jp_1005_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_box(0);
v_a_995_ = v___x_1025_;
goto v___jp_994_;
}
}
else
{
lean_object* v_a_1026_; 
lean_dec(v_val_1013_);
v_a_1026_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1016_, 1);
v_a_984_ = v_a_1026_;
goto v___jp_983_;
}
}
else
{
lean_object* v_a_1027_; 
lean_dec(v_val_1013_);
v_a_1027_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1014_, 1);
v_a_984_ = v_a_1027_;
goto v___jp_983_;
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_expectedType_x3f_970_);
v___x_1028_ = lean_box(0);
v_a_995_ = v___x_1028_;
goto v___jp_994_;
}
}
else
{
lean_dec(v_expectedType_x3f_970_);
v___y_1006_ = v___x_1012_;
goto v___jp_1005_;
}
}
else
{
lean_dec(v_a_981_);
lean_dec(v_expectedType_x3f_970_);
lean_dec(v_tac_969_);
return v___x_1009_;
}
v___jp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_981_, v___x_982_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_993_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
lean_ctor_set(v___x_987_, 0, v_a_984_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_984_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
lean_dec_ref(v_a_984_);
return v___x_985_;
}
}
v___jp_994_:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_981_, v___x_982_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1004_);
v___x_998_ = v___x_996_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_dec(v___x_996_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v_a_995_);
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_995_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
return v___x_996_;
}
}
v___jp_1005_:
{
if (lean_obj_tag(v___y_1006_) == 0)
{
lean_object* v_a_1007_; 
v_a_1007_ = lean_ctor_get(v___y_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___y_1006_, 1);
v_a_995_ = v_a_1007_;
goto v___jp_994_;
}
else
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___y_1006_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___y_1006_, 1);
v_a_984_ = v_a_1008_;
goto v___jp_983_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_expectedType_x3f_970_);
lean_dec(v_tac_969_);
lean_dec_ref(v_initialState_968_);
v_a_1029_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_980_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_980_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_0interp(lean_interpreter_value* stack)
{
lean_object* v_initialState_968_ = stack[0].m_obj;
lean_object* v_tac_969_ = stack[1].m_obj;
lean_object* v_expectedType_x3f_970_ = stack[2].m_obj;
lean_object* v_a_971_ = stack[3].m_obj;
lean_object* v_a_972_ = stack[4].m_obj;
lean_object* v_a_973_ = stack[5].m_obj;
lean_object* v_a_974_ = stack[6].m_obj;
lean_object* v_a_975_ = stack[7].m_obj;
lean_object* v_a_976_ = stack[8].m_obj;
lean_object* v_a_977_ = stack[9].m_obj;
lean_object* v_a_978_ = stack[10].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_968_, v_tac_969_, v_expectedType_x3f_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object* v_initialState_1038_, lean_object* v_tac_1039_, lean_object* v_expectedType_x3f_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1038_, v_tac_1039_, v_expectedType_x3f_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
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
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(lean_object* v_00_u03b1_1051_, lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_1052_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1052_ = stack[1].m_obj;
lean_object* v___y_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v___y_1057_ = stack[6].m_obj;
lean_object* v___y_1058_ = stack[7].m_obj;
lean_object* v___y_1059_ = stack[8].m_obj;
lean_object* v___y_1060_ = stack[9].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(lean_box(0), v_msg_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(v_00_u03b1_1064_, v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1075_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic(lean_object* v_initialState_1076_, lean_object* v_tac_1077_, lean_object* v_expectedType_x3f_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1080_, v_a_1082_, v_a_1084_, v_a_1086_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1076_, v_tac_1077_, v_expectedType_x3f_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1089_);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1090_, 0);
lean_dec(v_unused_1100_);
v___x_1092_ = v___x_1090_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v___x_1090_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = 1;
v___x_1095_ = lean_box(v___x_1094_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1130_; 
v_a_1101_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1103_ = v___x_1090_;
v_isShared_1104_ = v_isSharedCheck_1130_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1090_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1130_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___y_1106_; uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Exception_isInterrupt(v_a_1101_);
if (v___x_1128_ == 0)
{
uint8_t v___x_1129_; 
lean_inc(v_a_1101_);
v___x_1129_ = l_Lean_Exception_isRuntime(v_a_1101_);
v___y_1106_ = v___x_1129_;
goto v___jp_1105_;
}
else
{
v___y_1106_ = v___x_1128_;
goto v___jp_1105_;
}
v___jp_1105_:
{
if (v___y_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_del_object(v___x_1103_);
lean_dec(v_a_1101_);
v___x_1107_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1089_, v___y_1106_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1115_; 
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1107_, 0);
lean_dec(v_unused_1116_);
v___x_1109_ = v___x_1107_;
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v___x_1107_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_box(v___y_1106_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1107_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1107_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec(v_a_1089_);
if (v_isShared_1104_ == 0)
{
v___x_1126_ = v___x_1103_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1101_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_expectedType_x3f_1078_);
lean_dec(v_tac_1077_);
lean_dec_ref(v_initialState_1076_);
v_a_1131_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1088_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1088_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_isValidTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_initialState_1076_ = stack[0].m_obj;
lean_object* v_tac_1077_ = stack[1].m_obj;
lean_object* v_expectedType_x3f_1078_ = stack[2].m_obj;
lean_object* v_a_1079_ = stack[3].m_obj;
lean_object* v_a_1080_ = stack[4].m_obj;
lean_object* v_a_1081_ = stack[5].m_obj;
lean_object* v_a_1082_ = stack[6].m_obj;
lean_object* v_a_1083_ = stack[7].m_obj;
lean_object* v_a_1084_ = stack[8].m_obj;
lean_object* v_a_1085_ = stack[9].m_obj;
lean_object* v_a_1086_ = stack[10].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1076_, v_tac_1077_, v_expectedType_x3f_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic___boxed(lean_object* v_initialState_1140_, lean_object* v_tac_1141_, lean_object* v_expectedType_x3f_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1140_, v_tac_1141_, v_expectedType_x3f_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15));
v___x_1187_ = l_Lean_stringToMessageData(v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* v_tac_1190_, lean_object* v_msg_1191_, lean_object* v_initialState_1192_, lean_object* v_expectedType_x3f_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; 
lean_inc(v_expectedType_x3f_1193_);
lean_inc(v_tac_1190_);
lean_inc_ref(v_initialState_1192_);
v___x_1203_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1192_, v_tac_1190_, v_expectedType_x3f_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1263_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1263_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1263_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_unbox(v_a_1204_);
if (v___x_1208_ == 0)
{
lean_object* v_ref_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_del_object(v___x_1206_);
v_ref_1209_ = lean_ctor_get(v_a_1200_, 2);
v___x_1210_ = lean_unbox(v_a_1204_);
lean_dec(v_a_1204_);
v___x_1211_ = l_Lean_SourceInfo_fromRef(v_ref_1209_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2));
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3));
lean_inc_n(v___x_1211_, 8);
v___x_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1211_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5));
v___x_1216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7));
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11));
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12));
v___x_1220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1211_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_node1(v___x_1211_, v___x_1218_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13));
v___x_1223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1211_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_Syntax_node3(v___x_1211_, v___x_1217_, v___x_1221_, v___x_1223_, v_tac_1190_);
v___x_1225_ = l_Lean_Syntax_node1(v___x_1211_, v___x_1216_, v___x_1224_);
v___x_1226_ = l_Lean_Syntax_node1(v___x_1211_, v___x_1215_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1211_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node3(v___x_1211_, v___x_1212_, v___x_1214_, v___x_1226_, v___x_1228_);
lean_inc(v___x_1229_);
v___x_1230_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1192_, v___x_1229_, v_expectedType_x3f_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1249_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1249_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1249_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_unbox(v_a_1231_);
lean_dec(v_a_1231_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v___x_1229_);
lean_dec_ref(v_msg_1191_);
v___x_1236_ = lean_box(0);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_msg_1191_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1229_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1245_);
v___x_1247_ = v___x_1233_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v___x_1229_);
lean_dec_ref(v_msg_1191_);
v_a_1250_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1230_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1230_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
lean_dec(v_a_1204_);
lean_dec(v_expectedType_x3f_1193_);
lean_dec_ref(v_initialState_1192_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_tac_1190_);
lean_ctor_set(v___x_1258_, 1, v_msg_1191_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1259_);
v___x_1261_ = v___x_1206_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_expectedType_x3f_1193_);
lean_dec_ref(v_initialState_1192_);
lean_dec_ref(v_msg_1191_);
lean_dec(v_tac_1190_);
v_a_1264_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1203_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1203_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_tac_1190_ = stack[0].m_obj;
lean_object* v_msg_1191_ = stack[1].m_obj;
lean_object* v_initialState_1192_ = stack[2].m_obj;
lean_object* v_expectedType_x3f_1193_ = stack[3].m_obj;
lean_object* v_a_1194_ = stack[4].m_obj;
lean_object* v_a_1195_ = stack[5].m_obj;
lean_object* v_a_1196_ = stack[6].m_obj;
lean_object* v_a_1197_ = stack[7].m_obj;
lean_object* v_a_1198_ = stack[8].m_obj;
lean_object* v_a_1199_ = stack[9].m_obj;
lean_object* v_a_1200_ = stack[10].m_obj;
lean_object* v_a_1201_ = stack[11].m_obj;
lean_object* v_res_1272_;
v_res_1272_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_tac_1190_, v_msg_1191_, v_initialState_1192_, v_expectedType_x3f_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
stack->m_obj
 = v_res_1272_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object* v_tac_1273_, lean_object* v_msg_1274_, lean_object* v_initialState_1275_, lean_object* v_expectedType_x3f_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_tac_1273_, v_msg_1274_, v_initialState_1275_, v_expectedType_x3f_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* v_targetKind_1296_, lean_object* v_invalidTactic_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_targetKind_1296_);
v___x_1300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_indentD(v_invalidTactic_1297_);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
v___x_1305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0));
v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2));
v___x_1311_ = l_Lean_stringToMessageData(v___x_1310_);
return v___x_1311_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object* v_e_1324_, uint8_t v_useRefine_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_tac_1337_; lean_object* v___x_1346_; 
lean_inc_ref(v_e_1324_);
v___x_1346_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_1324_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1346_) == 0)
{
if (v_useRefine_1325_ == 0)
{
lean_object* v_a_1347_; lean_object* v_ref_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v_ref_1348_ = lean_ctor_get(v___y_1328_, 2);
v___x_1349_ = l_Lean_SourceInfo_fromRef(v_ref_1348_, v_useRefine_1325_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4));
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5));
lean_inc(v___x_1349_);
v___x_1352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
v___x_1353_ = l_Lean_Syntax_node2(v___x_1349_, v___x_1351_, v___x_1352_, v_a_1347_);
v_tac_1337_ = v___x_1353_;
goto v___jp_1336_;
}
else
{
lean_object* v_a_1354_; lean_object* v_ref_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1346_, 1);
v_ref_1355_ = lean_ctor_get(v___y_1328_, 2);
v___x_1356_ = 0;
v___x_1357_ = l_Lean_SourceInfo_fromRef(v_ref_1355_, v___x_1356_);
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6));
v___x_1359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7));
lean_inc(v___x_1357_);
v___x_1360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1357_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
v___x_1361_ = l_Lean_Syntax_node2(v___x_1357_, v___x_1359_, v___x_1360_, v_a_1354_);
v_tac_1337_ = v___x_1361_;
goto v___jp_1336_;
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_e_1324_);
v_a_1362_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1346_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1346_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
v___jp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___y_1332_);
lean_ctor_set(v___x_1334_, 1, v___y_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
v___jp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = l_Lean_MessageData_ofExpr(v_e_1324_);
v___x_1339_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1338_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (v_useRefine_1325_ == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_a_1340_);
v___y_1332_ = v_tac_1337_;
v___y_1333_ = v___x_1342_;
goto v___jp_1331_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_a_1343_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1339_);
v___x_1344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v_a_1343_);
v___y_1332_ = v_tac_1337_;
v___y_1333_ = v___x_1345_;
goto v___jp_1331_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1324_ = stack[0].m_obj;
uint8_t v_useRefine_1325_ = stack[1].m_num;
lean_object* v___y_1326_ = stack[2].m_obj;
lean_object* v___y_1327_ = stack[3].m_obj;
lean_object* v___y_1328_ = stack[4].m_obj;
lean_object* v___y_1329_ = stack[5].m_obj;
lean_object* v_res_1370_;
v_res_1370_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_1324_, v_useRefine_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
stack->m_obj
 = v_res_1370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object* v_e_1371_, lean_object* v_useRefine_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v_useRefine_boxed_1378_; lean_object* v_res_1379_; 
v_useRefine_boxed_1378_ = lean_unbox(v_useRefine_1372_);
v_res_1379_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_1371_, v_useRefine_boxed_1378_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1379_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* v_e_1380_, uint8_t v_useRefine_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_toCold_1387_; lean_object* v_currRecDepth_1388_; lean_object* v_ref_1389_; uint8_t v_suppressElabErrors_1390_; uint8_t v_isRecordingDeps_1391_; lean_object* v_fileName_1392_; lean_object* v_fileMap_1393_; lean_object* v_options_1394_; lean_object* v_currNamespace_1395_; lean_object* v_openDecls_1396_; lean_object* v_initHeartbeats_1397_; lean_object* v_maxHeartbeats_1398_; lean_object* v_quotContext_1399_; lean_object* v_currMacroScope_1400_; lean_object* v_cancelTk_x3f_1401_; lean_object* v_inheritedTraceOptions_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; uint16_t v___y_1406_; lean_object* v___y_1407_; lean_object* v_fileName_1408_; lean_object* v_fileMap_1409_; lean_object* v_currNamespace_1410_; lean_object* v_openDecls_1411_; lean_object* v_initHeartbeats_1412_; lean_object* v_maxHeartbeats_1413_; lean_object* v_quotContext_1414_; lean_object* v_currMacroScope_1415_; lean_object* v_cancelTk_x3f_1416_; lean_object* v_inheritedTraceOptions_1417_; lean_object* v_currRecDepth_1418_; lean_object* v_ref_1419_; uint8_t v_suppressElabErrors_1420_; uint8_t v_isRecordingDeps_1421_; lean_object* v___y_1422_; uint16_t v___y_1429_; uint8_t v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1454_; 
v_toCold_1387_ = lean_ctor_get(v_a_1384_, 0);
v_currRecDepth_1388_ = lean_ctor_get(v_a_1384_, 1);
v_ref_1389_ = lean_ctor_get(v_a_1384_, 2);
v_suppressElabErrors_1390_ = lean_ctor_get_uint8(v_a_1384_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1391_ = lean_ctor_get_uint8(v_a_1384_, sizeof(void*)*3 + 3);
v_fileName_1392_ = lean_ctor_get(v_toCold_1387_, 0);
v_fileMap_1393_ = lean_ctor_get(v_toCold_1387_, 1);
v_options_1394_ = lean_ctor_get(v_toCold_1387_, 2);
v_currNamespace_1395_ = lean_ctor_get(v_toCold_1387_, 4);
v_openDecls_1396_ = lean_ctor_get(v_toCold_1387_, 5);
v_initHeartbeats_1397_ = lean_ctor_get(v_toCold_1387_, 6);
v_maxHeartbeats_1398_ = lean_ctor_get(v_toCold_1387_, 7);
v_quotContext_1399_ = lean_ctor_get(v_toCold_1387_, 8);
v_currMacroScope_1400_ = lean_ctor_get(v_toCold_1387_, 9);
v_cancelTk_x3f_1401_ = lean_ctor_get(v_toCold_1387_, 10);
v_inheritedTraceOptions_1402_ = lean_ctor_get(v_toCold_1387_, 11);
v___x_1403_ = lean_box(v_useRefine_1381_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1404_, 0, v_e_1380_);
lean_closure_set(v___f_1404_, 1, v___x_1403_);
if (v_isRecordingDeps_1391_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = l_Lean_pp_mvars;
lean_inc_ref(v_options_1394_);
v___x_1466_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1394_, v___x_1465_, v_isRecordingDeps_1391_);
v___y_1454_ = v___x_1466_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1467_; 
lean_inc_ref(v_options_1394_);
v___x_1467_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1394_);
v___y_1454_ = v___x_1467_;
goto v___jp_1453_;
}
v___jp_1405_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1423_ = l_Lean_maxRecDepth;
v___x_1424_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v___y_1407_, v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1425_, 0, v_fileName_1408_);
lean_ctor_set(v___x_1425_, 1, v_fileMap_1409_);
lean_ctor_set(v___x_1425_, 2, v___y_1407_);
lean_ctor_set(v___x_1425_, 3, v___x_1424_);
lean_ctor_set(v___x_1425_, 4, v_currNamespace_1410_);
lean_ctor_set(v___x_1425_, 5, v_openDecls_1411_);
lean_ctor_set(v___x_1425_, 6, v_initHeartbeats_1412_);
lean_ctor_set(v___x_1425_, 7, v_maxHeartbeats_1413_);
lean_ctor_set(v___x_1425_, 8, v_quotContext_1414_);
lean_ctor_set(v___x_1425_, 9, v_currMacroScope_1415_);
lean_ctor_set(v___x_1425_, 10, v_cancelTk_x3f_1416_);
lean_ctor_set(v___x_1425_, 11, v_inheritedTraceOptions_1417_);
lean_inc(v_ref_1419_);
lean_inc(v_currRecDepth_1418_);
v___x_1426_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_currRecDepth_1418_);
lean_ctor_set(v___x_1426_, 2, v_ref_1419_);
lean_ctor_set_uint16(v___x_1426_, sizeof(void*)*3, v___y_1406_);
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*3 + 2, v_suppressElabErrors_1420_);
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*3 + 3, v_isRecordingDeps_1421_);
v___x_1427_ = l_Lean_Meta_withExposedNames___redArg(v___f_1404_, v_a_1382_, v_a_1383_, v___x_1426_, v___y_1422_);
lean_dec_ref_known(v___x_1426_, 3);
return v___x_1427_;
}
v___jp_1428_:
{
lean_object* v___x_1432_; lean_object* v_env_1433_; lean_object* v_nextMacroScope_1434_; lean_object* v_ngen_1435_; lean_object* v_auxDeclNGen_1436_; lean_object* v_traceState_1437_; lean_object* v_recordedDeps_1438_; lean_object* v_messages_1439_; lean_object* v_infoState_1440_; lean_object* v_snapshotTasks_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1451_; 
v___x_1432_ = lean_st_ref_take(v_a_1385_);
v_env_1433_ = lean_ctor_get(v___x_1432_, 0);
v_nextMacroScope_1434_ = lean_ctor_get(v___x_1432_, 1);
v_ngen_1435_ = lean_ctor_get(v___x_1432_, 2);
v_auxDeclNGen_1436_ = lean_ctor_get(v___x_1432_, 3);
v_traceState_1437_ = lean_ctor_get(v___x_1432_, 4);
v_recordedDeps_1438_ = lean_ctor_get(v___x_1432_, 6);
v_messages_1439_ = lean_ctor_get(v___x_1432_, 7);
v_infoState_1440_ = lean_ctor_get(v___x_1432_, 8);
v_snapshotTasks_1441_ = lean_ctor_get(v___x_1432_, 9);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1432_, 5);
lean_dec(v_unused_1452_);
v___x_1443_ = v___x_1432_;
v_isShared_1444_ = v_isSharedCheck_1451_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_snapshotTasks_1441_);
lean_inc(v_infoState_1440_);
lean_inc(v_messages_1439_);
lean_inc(v_recordedDeps_1438_);
lean_inc(v_traceState_1437_);
lean_inc(v_auxDeclNGen_1436_);
lean_inc(v_ngen_1435_);
lean_inc(v_nextMacroScope_1434_);
lean_inc(v_env_1433_);
lean_dec(v___x_1432_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1451_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1445_ = l_Lean_Kernel_enableDiag(v_env_1433_, v___y_1430_);
v___x_1446_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 5, v___x_1446_);
lean_ctor_set(v___x_1443_, 0, v___x_1445_);
v___x_1448_ = v___x_1443_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_nextMacroScope_1434_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_ngen_1435_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_auxDeclNGen_1436_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_traceState_1437_);
lean_ctor_set(v_reuseFailAlloc_1450_, 5, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1450_, 6, v_recordedDeps_1438_);
lean_ctor_set(v_reuseFailAlloc_1450_, 7, v_messages_1439_);
lean_ctor_set(v_reuseFailAlloc_1450_, 8, v_infoState_1440_);
lean_ctor_set(v_reuseFailAlloc_1450_, 9, v_snapshotTasks_1441_);
v___x_1448_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_st_ref_put(v_a_1385_, v___x_1448_);
lean_inc_ref(v_inheritedTraceOptions_1402_);
lean_inc(v_cancelTk_x3f_1401_);
lean_inc(v_currMacroScope_1400_);
lean_inc(v_quotContext_1399_);
lean_inc(v_maxHeartbeats_1398_);
lean_inc(v_initHeartbeats_1397_);
lean_inc(v_openDecls_1396_);
lean_inc(v_currNamespace_1395_);
lean_inc_ref(v_fileMap_1393_);
lean_inc_ref(v_fileName_1392_);
v___y_1406_ = v___y_1429_;
v___y_1407_ = v___y_1431_;
v_fileName_1408_ = v_fileName_1392_;
v_fileMap_1409_ = v_fileMap_1393_;
v_currNamespace_1410_ = v_currNamespace_1395_;
v_openDecls_1411_ = v_openDecls_1396_;
v_initHeartbeats_1412_ = v_initHeartbeats_1397_;
v_maxHeartbeats_1413_ = v_maxHeartbeats_1398_;
v_quotContext_1414_ = v_quotContext_1399_;
v_currMacroScope_1415_ = v_currMacroScope_1400_;
v_cancelTk_x3f_1416_ = v_cancelTk_x3f_1401_;
v_inheritedTraceOptions_1417_ = v_inheritedTraceOptions_1402_;
v_currRecDepth_1418_ = v_currRecDepth_1388_;
v_ref_1419_ = v_ref_1389_;
v_suppressElabErrors_1420_ = v_suppressElabErrors_1390_;
v_isRecordingDeps_1421_ = v_isRecordingDeps_1391_;
v___y_1422_ = v_a_1385_;
goto v___jp_1405_;
}
}
}
v___jp_1453_:
{
uint16_t v___x_1455_; lean_object* v___x_1456_; lean_object* v_env_1457_; uint8_t v___x_1458_; uint16_t v___x_1459_; uint16_t v___x_1460_; uint16_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1455_ = l_Lean_OptionFlags_ofOptions(v___y_1454_);
v___x_1456_ = lean_st_ref_get(v_a_1385_);
v_env_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1457_);
lean_dec_ref(v_env_1457_);
v___x_1459_ = 512;
v___x_1460_ = lean_uint16_land(v___x_1455_, v___x_1459_);
v___x_1461_ = 0;
v___x_1462_ = lean_uint16_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
if (v___x_1458_ == 0)
{
uint8_t v___x_1463_; 
v___x_1463_ = 1;
v___y_1429_ = v___x_1455_;
v___y_1430_ = v___x_1463_;
v___y_1431_ = v___y_1454_;
goto v___jp_1428_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1402_);
lean_inc(v_cancelTk_x3f_1401_);
lean_inc(v_currMacroScope_1400_);
lean_inc(v_quotContext_1399_);
lean_inc(v_maxHeartbeats_1398_);
lean_inc(v_initHeartbeats_1397_);
lean_inc(v_openDecls_1396_);
lean_inc(v_currNamespace_1395_);
lean_inc_ref(v_fileMap_1393_);
lean_inc_ref(v_fileName_1392_);
v___y_1406_ = v___x_1455_;
v___y_1407_ = v___y_1454_;
v_fileName_1408_ = v_fileName_1392_;
v_fileMap_1409_ = v_fileMap_1393_;
v_currNamespace_1410_ = v_currNamespace_1395_;
v_openDecls_1411_ = v_openDecls_1396_;
v_initHeartbeats_1412_ = v_initHeartbeats_1397_;
v_maxHeartbeats_1413_ = v_maxHeartbeats_1398_;
v_quotContext_1414_ = v_quotContext_1399_;
v_currMacroScope_1415_ = v_currMacroScope_1400_;
v_cancelTk_x3f_1416_ = v_cancelTk_x3f_1401_;
v_inheritedTraceOptions_1417_ = v_inheritedTraceOptions_1402_;
v_currRecDepth_1418_ = v_currRecDepth_1388_;
v_ref_1419_ = v_ref_1389_;
v_suppressElabErrors_1420_ = v_suppressElabErrors_1390_;
v_isRecordingDeps_1421_ = v_isRecordingDeps_1391_;
v___y_1422_ = v_a_1385_;
goto v___jp_1405_;
}
}
else
{
if (v___x_1458_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1402_);
lean_inc(v_cancelTk_x3f_1401_);
lean_inc(v_currMacroScope_1400_);
lean_inc(v_quotContext_1399_);
lean_inc(v_maxHeartbeats_1398_);
lean_inc(v_initHeartbeats_1397_);
lean_inc(v_openDecls_1396_);
lean_inc(v_currNamespace_1395_);
lean_inc_ref(v_fileMap_1393_);
lean_inc_ref(v_fileName_1392_);
v___y_1406_ = v___x_1455_;
v___y_1407_ = v___y_1454_;
v_fileName_1408_ = v_fileName_1392_;
v_fileMap_1409_ = v_fileMap_1393_;
v_currNamespace_1410_ = v_currNamespace_1395_;
v_openDecls_1411_ = v_openDecls_1396_;
v_initHeartbeats_1412_ = v_initHeartbeats_1397_;
v_maxHeartbeats_1413_ = v_maxHeartbeats_1398_;
v_quotContext_1414_ = v_quotContext_1399_;
v_currMacroScope_1415_ = v_currMacroScope_1400_;
v_cancelTk_x3f_1416_ = v_cancelTk_x3f_1401_;
v_inheritedTraceOptions_1417_ = v_inheritedTraceOptions_1402_;
v_currRecDepth_1418_ = v_currRecDepth_1388_;
v_ref_1419_ = v_ref_1389_;
v_suppressElabErrors_1420_ = v_suppressElabErrors_1390_;
v_isRecordingDeps_1421_ = v_isRecordingDeps_1391_;
v___y_1422_ = v_a_1385_;
goto v___jp_1405_;
}
else
{
uint8_t v___x_1464_; 
v___x_1464_ = 0;
v___y_1429_ = v___x_1455_;
v___y_1430_ = v___x_1464_;
v___y_1431_ = v___y_1454_;
goto v___jp_1428_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1380_ = stack[0].m_obj;
uint8_t v_useRefine_1381_ = stack[1].m_num;
lean_object* v_a_1382_ = stack[2].m_obj;
lean_object* v_a_1383_ = stack[3].m_obj;
lean_object* v_a_1384_ = stack[4].m_obj;
lean_object* v_a_1385_ = stack[5].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1380_, v_useRefine_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* v_e_1469_, lean_object* v_useRefine_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_useRefine_boxed_1476_; lean_object* v_res_1477_; 
v_useRefine_boxed_1476_ = lean_unbox(v_useRefine_1470_);
v_res_1477_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1469_, v_useRefine_boxed_1476_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1477_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(lean_object* v_as_1481_, size_t v_sz_1482_, size_t v_i_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1483_, v_sz_1482_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1484_);
return v___x_1491_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1493_; 
v_a_1492_ = lean_array_uget_borrowed(v_as_1481_, v_i_1483_);
lean_inc(v_a_1492_);
v___x_1493_ = l_Lean_MVarId_getType(v_a_1492_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_1494_, v___y_1486_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___boxed), 6, 1);
lean_closure_set(v___x_1497_, 0, v_a_1496_);
v___x_1498_ = l_Lean_Meta_withExposedNames___redArg(v___x_1497_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1));
v___x_1501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1499_);
v___x_1502_ = l_Std_Format_defWidth;
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = l_Std_Format_pretty(v___x_1501_, v___x_1502_, v___x_1503_, v___x_1503_);
v___x_1505_ = lean_string_append(v_b_1484_, v___x_1504_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1483_, v___x_1506_);
v_i_1483_ = v___x_1507_;
v_b_1484_ = v___x_1505_;
goto _start;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v_b_1484_);
v_a_1509_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1498_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1498_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_b_1484_);
v_a_1517_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1495_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1495_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v_b_1484_);
v_a_1525_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1493_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1493_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1481_ = stack[0].m_obj;
size_t v_sz_1482_ = stack[1].m_num;
size_t v_i_1483_ = stack[2].m_num;
lean_object* v_b_1484_ = stack[3].m_obj;
lean_object* v___y_1485_ = stack[4].m_obj;
lean_object* v___y_1486_ = stack[5].m_obj;
lean_object* v___y_1487_ = stack[6].m_obj;
lean_object* v___y_1488_ = stack[7].m_obj;
lean_object* v_res_1533_;
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1481_, v_sz_1482_, v_i_1483_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
stack->m_obj
 = v_res_1533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(lean_object* v_as_1534_, lean_object* v_sz_1535_, lean_object* v_i_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1535_);
lean_dec(v_sz_1535_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1536_);
lean_dec(v_i_1536_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1534_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_as_1534_);
return v_res_1545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0));
v___x_1548_ = l_Lean_stringToMessageData(v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t v_addSubgoalsMsg_1557_, lean_object* v_checkState_x3f_1558_, lean_object* v_e_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v_postInfo_x3f_1583_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; uint8_t v___y_1600_; uint16_t v___y_1686_; lean_object* v___y_1687_; lean_object* v_fileName_1688_; lean_object* v_fileMap_1689_; lean_object* v_currNamespace_1690_; lean_object* v_openDecls_1691_; lean_object* v_initHeartbeats_1692_; lean_object* v_maxHeartbeats_1693_; lean_object* v_quotContext_1694_; lean_object* v_currMacroScope_1695_; lean_object* v_cancelTk_x3f_1696_; lean_object* v_inheritedTraceOptions_1697_; lean_object* v_currRecDepth_1698_; lean_object* v_ref_1699_; uint8_t v_suppressElabErrors_1700_; uint8_t v_isRecordingDeps_1701_; lean_object* v___y_1702_; lean_object* v_toCold_1722_; lean_object* v_currRecDepth_1723_; lean_object* v_ref_1724_; uint8_t v_suppressElabErrors_1725_; uint8_t v_isRecordingDeps_1726_; lean_object* v_fileName_1727_; lean_object* v_fileMap_1728_; lean_object* v_options_1729_; lean_object* v_currNamespace_1730_; lean_object* v_openDecls_1731_; lean_object* v_initHeartbeats_1732_; lean_object* v_maxHeartbeats_1733_; lean_object* v_quotContext_1734_; lean_object* v_currMacroScope_1735_; lean_object* v_cancelTk_x3f_1736_; lean_object* v_inheritedTraceOptions_1737_; uint16_t v___y_1739_; uint8_t v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1764_; 
v_toCold_1722_ = lean_ctor_get(v_a_1566_, 0);
v_currRecDepth_1723_ = lean_ctor_get(v_a_1566_, 1);
v_ref_1724_ = lean_ctor_get(v_a_1566_, 2);
v_suppressElabErrors_1725_ = lean_ctor_get_uint8(v_a_1566_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1726_ = lean_ctor_get_uint8(v_a_1566_, sizeof(void*)*3 + 3);
v_fileName_1727_ = lean_ctor_get(v_toCold_1722_, 0);
v_fileMap_1728_ = lean_ctor_get(v_toCold_1722_, 1);
v_options_1729_ = lean_ctor_get(v_toCold_1722_, 2);
v_currNamespace_1730_ = lean_ctor_get(v_toCold_1722_, 4);
v_openDecls_1731_ = lean_ctor_get(v_toCold_1722_, 5);
v_initHeartbeats_1732_ = lean_ctor_get(v_toCold_1722_, 6);
v_maxHeartbeats_1733_ = lean_ctor_get(v_toCold_1722_, 7);
v_quotContext_1734_ = lean_ctor_get(v_toCold_1722_, 8);
v_currMacroScope_1735_ = lean_ctor_get(v_toCold_1722_, 9);
v_cancelTk_x3f_1736_ = lean_ctor_get(v_toCold_1722_, 10);
v_inheritedTraceOptions_1737_ = lean_ctor_get(v_toCold_1722_, 11);
if (v_isRecordingDeps_1726_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = l_Lean_pp_mvars;
lean_inc_ref(v_options_1729_);
v___x_1776_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1729_, v___x_1775_, v_isRecordingDeps_1726_);
v___y_1764_ = v___x_1776_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1777_; 
lean_inc_ref(v_options_1729_);
v___x_1777_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1729_);
v___y_1764_ = v___x_1777_;
goto v___jp_1763_;
}
v___jp_1569_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_inc_ref(v___y_1572_);
v___x_1573_ = l_Lean_stringToMessageData(v___y_1572_);
lean_inc_ref(v___y_1570_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___y_1570_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_1576_, v___y_1571_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
v___jp_1580_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___y_1581_);
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___y_1582_);
v___x_1588_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1585_);
lean_ctor_set(v___x_1588_, 1, v___x_1586_);
lean_ctor_set(v___x_1588_, 2, v_postInfo_x3f_1583_);
lean_ctor_set(v___x_1588_, 3, v___x_1586_);
lean_ctor_set(v___x_1588_, 4, v___x_1587_);
lean_ctor_set(v___x_1588_, 5, v___x_1586_);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
v___jp_1591_:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_box(0);
v___y_1581_ = v___y_1592_;
v___y_1582_ = v___y_1593_;
v_postInfo_x3f_1583_ = v___x_1594_;
goto v___jp_1580_;
}
v___jp_1595_:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1559_, v___y_1600_, v_a_1564_, v_a_1565_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1676_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1676_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1676_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
if (lean_obj_tag(v_checkState_x3f_1558_) == 1)
{
lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1659_; 
lean_del_object(v___x_1604_);
v_fst_1606_ = lean_ctor_get(v_a_1602_, 0);
v_snd_1607_ = lean_ctor_get(v_a_1602_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1609_ = v_a_1602_;
v_isShared_1610_ = v_isSharedCheck_1659_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_inc(v_fst_1606_);
lean_dec(v_a_1602_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1659_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_val_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_val_1611_ = lean_ctor_get(v_checkState_x3f_1558_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v_checkState_x3f_1558_, 1);
v___x_1612_ = lean_box(0);
lean_inc(v_snd_1607_);
v___x_1613_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_1606_, v_snd_1607_, v_val_1611_, v___x_1612_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
if (lean_obj_tag(v_a_1614_) == 1)
{
lean_object* v_val_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1641_; 
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
v_val_1615_ = lean_ctor_get(v_a_1614_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1614_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1617_ = v_a_1614_;
v_isShared_1618_ = v_isSharedCheck_1641_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_val_1615_);
lean_dec(v_a_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1641_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
if (v_addSubgoalsMsg_1557_ == 0)
{
lean_object* v_fst_1619_; lean_object* v_snd_1620_; 
lean_del_object(v___x_1617_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
v_fst_1619_ = lean_ctor_get(v_val_1615_, 0);
lean_inc(v_fst_1619_);
v_snd_1620_ = lean_ctor_get(v_val_1615_, 1);
lean_inc(v_snd_1620_);
lean_dec(v_val_1615_);
v___y_1592_ = v_fst_1619_;
v___y_1593_ = v_snd_1620_;
goto v___jp_1591_;
}
else
{
if (v___y_1596_ == 0)
{
lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1623_; size_t v_sz_1624_; size_t v___x_1625_; lean_object* v___x_1626_; 
v_fst_1621_ = lean_ctor_get(v_val_1615_, 0);
lean_inc(v_fst_1621_);
v_snd_1622_ = lean_ctor_get(v_val_1615_, 1);
lean_inc(v_snd_1622_);
lean_dec(v_val_1615_);
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4));
v_sz_1624_ = lean_array_size(v___y_1597_);
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v___y_1597_, v_sz_1624_, v___x_1625_, v___x_1623_, v_a_1564_, v_a_1565_, v___y_1598_, v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_a_1627_);
v___x_1629_ = v___x_1617_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
v___y_1581_ = v_fst_1621_;
v___y_1582_ = v_snd_1622_;
v_postInfo_x3f_1583_ = v___x_1629_;
goto v___jp_1580_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_snd_1622_);
lean_dec(v_fst_1621_);
lean_del_object(v___x_1617_);
v_a_1631_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1626_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1626_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; 
lean_del_object(v___x_1617_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
v_fst_1639_ = lean_ctor_get(v_val_1615_, 0);
lean_inc(v_fst_1639_);
v_snd_1640_ = lean_ctor_get(v_val_1615_, 1);
lean_inc(v_snd_1640_);
lean_dec(v_val_1615_);
v___y_1592_ = v_fst_1639_;
v___y_1593_ = v_snd_1640_;
goto v___jp_1591_;
}
}
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_dec(v_a_1614_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 7);
lean_ctor_set(v___x_1609_, 0, v___x_1642_);
v___x_1644_ = v___x_1609_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_snd_1607_);
v___x_1644_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6);
if (v___y_1600_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_1570_ = v___x_1647_;
v___y_1571_ = v___x_1646_;
v___y_1572_ = v___x_1648_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7));
v___y_1570_ = v___x_1647_;
v___y_1571_ = v___x_1646_;
v___y_1572_ = v___x_1649_;
goto v___jp_1569_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
v_a_1651_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1613_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1613_);
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
else
{
lean_object* v_fst_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v_checkState_x3f_1558_);
v_fst_1660_ = lean_ctor_get(v_a_1602_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v_a_1602_, 1);
lean_dec(v_unused_1675_);
v___x_1662_ = v_a_1602_;
v_isShared_1663_ = v_isSharedCheck_1674_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_fst_1660_);
lean_dec(v_a_1602_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1674_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_fst_1660_);
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_fst_1660_);
v___x_1666_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
lean_ctor_set(v___x_1668_, 2, v___x_1667_);
lean_ctor_set(v___x_1668_, 3, v___x_1667_);
lean_ctor_set(v___x_1668_, 4, v___x_1667_);
lean_ctor_set(v___x_1668_, 5, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1669_);
v___x_1671_ = v___x_1604_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec_ref(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v_checkState_x3f_1558_);
v_a_1677_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1601_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1601_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
v___jp_1685_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1703_ = l_Lean_maxRecDepth;
v___x_1704_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v___y_1687_, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1705_, 0, v_fileName_1688_);
lean_ctor_set(v___x_1705_, 1, v_fileMap_1689_);
lean_ctor_set(v___x_1705_, 2, v___y_1687_);
lean_ctor_set(v___x_1705_, 3, v___x_1704_);
lean_ctor_set(v___x_1705_, 4, v_currNamespace_1690_);
lean_ctor_set(v___x_1705_, 5, v_openDecls_1691_);
lean_ctor_set(v___x_1705_, 6, v_initHeartbeats_1692_);
lean_ctor_set(v___x_1705_, 7, v_maxHeartbeats_1693_);
lean_ctor_set(v___x_1705_, 8, v_quotContext_1694_);
lean_ctor_set(v___x_1705_, 9, v_currMacroScope_1695_);
lean_ctor_set(v___x_1705_, 10, v_cancelTk_x3f_1696_);
lean_ctor_set(v___x_1705_, 11, v_inheritedTraceOptions_1697_);
lean_inc(v_ref_1699_);
lean_inc(v_currRecDepth_1698_);
v___x_1706_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v_currRecDepth_1698_);
lean_ctor_set(v___x_1706_, 2, v_ref_1699_);
lean_ctor_set_uint16(v___x_1706_, sizeof(void*)*3, v___y_1686_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*3 + 2, v_suppressElabErrors_1700_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*3 + 3, v_isRecordingDeps_1701_);
lean_inc_ref(v_e_1559_);
v___x_1707_ = l_Lean_Meta_getMVars(v_e_1559_, v_a_1564_, v_a_1565_, v___x_1706_, v___y_1702_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = lean_array_get_size(v_a_1708_);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_nat_dec_eq(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
uint8_t v___x_1712_; 
v___x_1712_ = 1;
v___y_1596_ = v___x_1711_;
v___y_1597_ = v_a_1708_;
v___y_1598_ = v___x_1706_;
v___y_1599_ = v___y_1702_;
v___y_1600_ = v___x_1712_;
goto v___jp_1595_;
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = 0;
v___y_1596_ = v___x_1711_;
v___y_1597_ = v_a_1708_;
v___y_1598_ = v___x_1706_;
v___y_1599_ = v___y_1702_;
v___y_1600_ = v___x_1713_;
goto v___jp_1595_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref_known(v___x_1706_, 3);
lean_dec_ref(v_e_1559_);
lean_dec(v_checkState_x3f_1558_);
v_a_1714_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1707_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1707_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
v___jp_1738_:
{
lean_object* v___x_1742_; lean_object* v_env_1743_; lean_object* v_nextMacroScope_1744_; lean_object* v_ngen_1745_; lean_object* v_auxDeclNGen_1746_; lean_object* v_traceState_1747_; lean_object* v_recordedDeps_1748_; lean_object* v_messages_1749_; lean_object* v_infoState_1750_; lean_object* v_snapshotTasks_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1761_; 
v___x_1742_ = lean_st_ref_take(v_a_1567_);
v_env_1743_ = lean_ctor_get(v___x_1742_, 0);
v_nextMacroScope_1744_ = lean_ctor_get(v___x_1742_, 1);
v_ngen_1745_ = lean_ctor_get(v___x_1742_, 2);
v_auxDeclNGen_1746_ = lean_ctor_get(v___x_1742_, 3);
v_traceState_1747_ = lean_ctor_get(v___x_1742_, 4);
v_recordedDeps_1748_ = lean_ctor_get(v___x_1742_, 6);
v_messages_1749_ = lean_ctor_get(v___x_1742_, 7);
v_infoState_1750_ = lean_ctor_get(v___x_1742_, 8);
v_snapshotTasks_1751_ = lean_ctor_get(v___x_1742_, 9);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v___x_1742_, 5);
lean_dec(v_unused_1762_);
v___x_1753_ = v___x_1742_;
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_snapshotTasks_1751_);
lean_inc(v_infoState_1750_);
lean_inc(v_messages_1749_);
lean_inc(v_recordedDeps_1748_);
lean_inc(v_traceState_1747_);
lean_inc(v_auxDeclNGen_1746_);
lean_inc(v_ngen_1745_);
lean_inc(v_nextMacroScope_1744_);
lean_inc(v_env_1743_);
lean_dec(v___x_1742_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1755_ = l_Lean_Kernel_enableDiag(v_env_1743_, v___y_1740_);
v___x_1756_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 5, v___x_1756_);
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_nextMacroScope_1744_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_ngen_1745_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_auxDeclNGen_1746_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_traceState_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v_recordedDeps_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_messages_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_infoState_1750_);
lean_ctor_set(v_reuseFailAlloc_1760_, 9, v_snapshotTasks_1751_);
v___x_1758_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_st_ref_put(v_a_1567_, v___x_1758_);
lean_inc_ref(v_inheritedTraceOptions_1737_);
lean_inc(v_cancelTk_x3f_1736_);
lean_inc(v_currMacroScope_1735_);
lean_inc(v_quotContext_1734_);
lean_inc(v_maxHeartbeats_1733_);
lean_inc(v_initHeartbeats_1732_);
lean_inc(v_openDecls_1731_);
lean_inc(v_currNamespace_1730_);
lean_inc_ref(v_fileMap_1728_);
lean_inc_ref(v_fileName_1727_);
v___y_1686_ = v___y_1739_;
v___y_1687_ = v___y_1741_;
v_fileName_1688_ = v_fileName_1727_;
v_fileMap_1689_ = v_fileMap_1728_;
v_currNamespace_1690_ = v_currNamespace_1730_;
v_openDecls_1691_ = v_openDecls_1731_;
v_initHeartbeats_1692_ = v_initHeartbeats_1732_;
v_maxHeartbeats_1693_ = v_maxHeartbeats_1733_;
v_quotContext_1694_ = v_quotContext_1734_;
v_currMacroScope_1695_ = v_currMacroScope_1735_;
v_cancelTk_x3f_1696_ = v_cancelTk_x3f_1736_;
v_inheritedTraceOptions_1697_ = v_inheritedTraceOptions_1737_;
v_currRecDepth_1698_ = v_currRecDepth_1723_;
v_ref_1699_ = v_ref_1724_;
v_suppressElabErrors_1700_ = v_suppressElabErrors_1725_;
v_isRecordingDeps_1701_ = v_isRecordingDeps_1726_;
v___y_1702_ = v_a_1567_;
goto v___jp_1685_;
}
}
}
v___jp_1763_:
{
uint16_t v___x_1765_; lean_object* v___x_1766_; lean_object* v_env_1767_; uint8_t v___x_1768_; uint16_t v___x_1769_; uint16_t v___x_1770_; uint16_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1765_ = l_Lean_OptionFlags_ofOptions(v___y_1764_);
v___x_1766_ = lean_st_ref_get(v_a_1567_);
v_env_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc_ref(v_env_1767_);
lean_dec(v___x_1766_);
v___x_1768_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1767_);
lean_dec_ref(v_env_1767_);
v___x_1769_ = 512;
v___x_1770_ = lean_uint16_land(v___x_1765_, v___x_1769_);
v___x_1771_ = 0;
v___x_1772_ = lean_uint16_dec_eq(v___x_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
if (v___x_1768_ == 0)
{
uint8_t v___x_1773_; 
v___x_1773_ = 1;
v___y_1739_ = v___x_1765_;
v___y_1740_ = v___x_1773_;
v___y_1741_ = v___y_1764_;
goto v___jp_1738_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1737_);
lean_inc(v_cancelTk_x3f_1736_);
lean_inc(v_currMacroScope_1735_);
lean_inc(v_quotContext_1734_);
lean_inc(v_maxHeartbeats_1733_);
lean_inc(v_initHeartbeats_1732_);
lean_inc(v_openDecls_1731_);
lean_inc(v_currNamespace_1730_);
lean_inc_ref(v_fileMap_1728_);
lean_inc_ref(v_fileName_1727_);
v___y_1686_ = v___x_1765_;
v___y_1687_ = v___y_1764_;
v_fileName_1688_ = v_fileName_1727_;
v_fileMap_1689_ = v_fileMap_1728_;
v_currNamespace_1690_ = v_currNamespace_1730_;
v_openDecls_1691_ = v_openDecls_1731_;
v_initHeartbeats_1692_ = v_initHeartbeats_1732_;
v_maxHeartbeats_1693_ = v_maxHeartbeats_1733_;
v_quotContext_1694_ = v_quotContext_1734_;
v_currMacroScope_1695_ = v_currMacroScope_1735_;
v_cancelTk_x3f_1696_ = v_cancelTk_x3f_1736_;
v_inheritedTraceOptions_1697_ = v_inheritedTraceOptions_1737_;
v_currRecDepth_1698_ = v_currRecDepth_1723_;
v_ref_1699_ = v_ref_1724_;
v_suppressElabErrors_1700_ = v_suppressElabErrors_1725_;
v_isRecordingDeps_1701_ = v_isRecordingDeps_1726_;
v___y_1702_ = v_a_1567_;
goto v___jp_1685_;
}
}
else
{
if (v___x_1768_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1737_);
lean_inc(v_cancelTk_x3f_1736_);
lean_inc(v_currMacroScope_1735_);
lean_inc(v_quotContext_1734_);
lean_inc(v_maxHeartbeats_1733_);
lean_inc(v_initHeartbeats_1732_);
lean_inc(v_openDecls_1731_);
lean_inc(v_currNamespace_1730_);
lean_inc_ref(v_fileMap_1728_);
lean_inc_ref(v_fileName_1727_);
v___y_1686_ = v___x_1765_;
v___y_1687_ = v___y_1764_;
v_fileName_1688_ = v_fileName_1727_;
v_fileMap_1689_ = v_fileMap_1728_;
v_currNamespace_1690_ = v_currNamespace_1730_;
v_openDecls_1691_ = v_openDecls_1731_;
v_initHeartbeats_1692_ = v_initHeartbeats_1732_;
v_maxHeartbeats_1693_ = v_maxHeartbeats_1733_;
v_quotContext_1694_ = v_quotContext_1734_;
v_currMacroScope_1695_ = v_currMacroScope_1735_;
v_cancelTk_x3f_1696_ = v_cancelTk_x3f_1736_;
v_inheritedTraceOptions_1697_ = v_inheritedTraceOptions_1737_;
v_currRecDepth_1698_ = v_currRecDepth_1723_;
v_ref_1699_ = v_ref_1724_;
v_suppressElabErrors_1700_ = v_suppressElabErrors_1725_;
v_isRecordingDeps_1701_ = v_isRecordingDeps_1726_;
v___y_1702_ = v_a_1567_;
goto v___jp_1685_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = 0;
v___y_1739_ = v___x_1765_;
v___y_1740_ = v___x_1774_;
v___y_1741_ = v___y_1764_;
goto v___jp_1738_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_0interp(lean_interpreter_value* stack)
{
uint8_t v_addSubgoalsMsg_1557_ = stack[0].m_num;
lean_object* v_checkState_x3f_1558_ = stack[1].m_obj;
lean_object* v_e_1559_ = stack[2].m_obj;
lean_object* v_a_1560_ = stack[3].m_obj;
lean_object* v_a_1561_ = stack[4].m_obj;
lean_object* v_a_1562_ = stack[5].m_obj;
lean_object* v_a_1563_ = stack[6].m_obj;
lean_object* v_a_1564_ = stack[7].m_obj;
lean_object* v_a_1565_ = stack[8].m_obj;
lean_object* v_a_1566_ = stack[9].m_obj;
lean_object* v_a_1567_ = stack[10].m_obj;
lean_object* v_res_1778_;
v_res_1778_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_1557_, v_checkState_x3f_1558_, v_e_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
stack->m_obj
 = v_res_1778_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* v_addSubgoalsMsg_1779_, lean_object* v_checkState_x3f_1780_, lean_object* v_e_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1791_; lean_object* v_res_1792_; 
v_addSubgoalsMsg_boxed_1791_ = lean_unbox(v_addSubgoalsMsg_1779_);
v_res_1792_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_boxed_1791_, v_checkState_x3f_1780_, v_e_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1792_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object* v_as_1793_, size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1793_, v_sz_1794_, v_i_1795_, v_b_1796_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1793_ = stack[0].m_obj;
size_t v_sz_1794_ = stack[1].m_num;
size_t v_i_1795_ = stack[2].m_num;
lean_object* v_b_1796_ = stack[3].m_obj;
lean_object* v___y_1797_ = stack[4].m_obj;
lean_object* v___y_1798_ = stack[5].m_obj;
lean_object* v___y_1799_ = stack[6].m_obj;
lean_object* v___y_1800_ = stack[7].m_obj;
lean_object* v___y_1801_ = stack[8].m_obj;
lean_object* v___y_1802_ = stack[9].m_obj;
lean_object* v___y_1803_ = stack[10].m_obj;
lean_object* v___y_1804_ = stack[11].m_obj;
lean_object* v_res_1807_;
v_res_1807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_1793_, v_sz_1794_, v_i_1795_, v_b_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object* v_as_1808_, lean_object* v_sz_1809_, lean_object* v_i_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
size_t v_sz_boxed_1821_; size_t v_i_boxed_1822_; lean_object* v_res_1823_; 
v_sz_boxed_1821_ = lean_unbox_usize(v_sz_1809_);
lean_dec(v_sz_1809_);
v_i_boxed_1822_ = lean_unbox_usize(v_i_1810_);
lean_dec(v_i_1810_);
v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_1808_, v_sz_boxed_1821_, v_i_boxed_1822_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_as_1808_);
return v_res_1823_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1824_, lean_object* v_msgData_1825_, uint8_t v_severity_1826_, uint8_t v_isSilent_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
uint8_t v___y_1834_; lean_object* v___y_1835_; uint8_t v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v_toCold_1841_; lean_object* v___y_1842_; lean_object* v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1873_; uint8_t v___y_1874_; lean_object* v___y_1875_; uint8_t v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1898_; lean_object* v___y_1899_; uint8_t v___y_1900_; uint8_t v___y_1901_; lean_object* v___y_1902_; uint8_t v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1908_; uint8_t v___y_1909_; uint8_t v___y_1910_; uint8_t v___x_1921_; uint8_t v___y_1923_; uint8_t v___y_1924_; uint8_t v___y_1925_; uint8_t v___y_1927_; uint8_t v___x_1935_; 
v___x_1921_ = 2;
v___x_1935_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1826_, v___x_1921_);
if (v___x_1935_ == 0)
{
v___y_1927_ = v___x_1935_;
goto v___jp_1926_;
}
else
{
uint8_t v___x_1936_; 
lean_inc_ref(v_msgData_1825_);
v___x_1936_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1825_);
v___y_1927_ = v___x_1936_;
goto v___jp_1926_;
}
v___jp_1833_:
{
lean_object* v_currNamespace_1843_; lean_object* v_openDecls_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v_env_1849_; lean_object* v_nextMacroScope_1850_; lean_object* v_ngen_1851_; lean_object* v_auxDeclNGen_1852_; lean_object* v_traceState_1853_; lean_object* v_cache_1854_; lean_object* v_recordedDeps_1855_; lean_object* v_messages_1856_; lean_object* v_infoState_1857_; lean_object* v_snapshotTasks_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1869_; 
v_currNamespace_1843_ = lean_ctor_get(v_toCold_1841_, 4);
v_openDecls_1844_ = lean_ctor_get(v_toCold_1841_, 5);
lean_inc(v_openDecls_1844_);
lean_inc(v_currNamespace_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_currNamespace_1843_);
lean_ctor_set(v___x_1845_, 1, v_openDecls_1844_);
v___x_1846_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v___y_1839_);
lean_inc_ref(v___y_1835_);
lean_inc_ref(v___y_1840_);
v___x_1847_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1847_, 0, v___y_1840_);
lean_ctor_set(v___x_1847_, 1, v___y_1838_);
lean_ctor_set(v___x_1847_, 2, v___y_1837_);
lean_ctor_set(v___x_1847_, 3, v___y_1835_);
lean_ctor_set(v___x_1847_, 4, v___x_1846_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*5, v___y_1836_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*5 + 1, v___y_1834_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*5 + 2, v_isSilent_1827_);
v___x_1848_ = lean_st_ref_take(v___y_1842_);
v_env_1849_ = lean_ctor_get(v___x_1848_, 0);
v_nextMacroScope_1850_ = lean_ctor_get(v___x_1848_, 1);
v_ngen_1851_ = lean_ctor_get(v___x_1848_, 2);
v_auxDeclNGen_1852_ = lean_ctor_get(v___x_1848_, 3);
v_traceState_1853_ = lean_ctor_get(v___x_1848_, 4);
v_cache_1854_ = lean_ctor_get(v___x_1848_, 5);
v_recordedDeps_1855_ = lean_ctor_get(v___x_1848_, 6);
v_messages_1856_ = lean_ctor_get(v___x_1848_, 7);
v_infoState_1857_ = lean_ctor_get(v___x_1848_, 8);
v_snapshotTasks_1858_ = lean_ctor_get(v___x_1848_, 9);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1860_ = v___x_1848_;
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snapshotTasks_1858_);
lean_inc(v_infoState_1857_);
lean_inc(v_messages_1856_);
lean_inc(v_recordedDeps_1855_);
lean_inc(v_cache_1854_);
lean_inc(v_traceState_1853_);
lean_inc(v_auxDeclNGen_1852_);
lean_inc(v_ngen_1851_);
lean_inc(v_nextMacroScope_1850_);
lean_inc(v_env_1849_);
lean_dec(v___x_1848_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1862_ = lean_box(0);
v___x_1863_ = l_Lean_MessageLog_add(v___x_1847_, v_messages_1856_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 7, v___x_1863_);
v___x_1865_ = v___x_1860_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_env_1849_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_nextMacroScope_1850_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_ngen_1851_);
lean_ctor_set(v_reuseFailAlloc_1868_, 3, v_auxDeclNGen_1852_);
lean_ctor_set(v_reuseFailAlloc_1868_, 4, v_traceState_1853_);
lean_ctor_set(v_reuseFailAlloc_1868_, 5, v_cache_1854_);
lean_ctor_set(v_reuseFailAlloc_1868_, 6, v_recordedDeps_1855_);
lean_ctor_set(v_reuseFailAlloc_1868_, 7, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1868_, 8, v_infoState_1857_);
lean_ctor_set(v_reuseFailAlloc_1868_, 9, v_snapshotTasks_1858_);
v___x_1865_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_st_ref_put(v___y_1842_, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1862_);
return v___x_1867_;
}
}
}
v___jp_1870_:
{
lean_object* v_fileName_1879_; lean_object* v_fileMap_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1896_; 
v_fileName_1879_ = lean_ctor_get(v___y_1877_, 0);
v_fileMap_1880_ = lean_ctor_get(v___y_1877_, 1);
v___x_1881_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1825_);
v___x_1882_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1881_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_inc_ref_n(v_fileMap_1880_, 2);
v___x_1887_ = l_Lean_FileMap_toPosition(v_fileMap_1880_, v___y_1875_);
lean_dec(v___y_1875_);
v___x_1888_ = l_Lean_FileMap_toPosition(v_fileMap_1880_, v___y_1878_);
lean_dec(v___y_1878_);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_1876_ == 0)
{
lean_del_object(v___x_1885_);
lean_dec_ref(v___y_1871_);
v___y_1834_ = v___y_1873_;
v___y_1835_ = v___x_1890_;
v___y_1836_ = v___y_1874_;
v___y_1837_ = v___x_1889_;
v___y_1838_ = v___x_1887_;
v___y_1839_ = v_a_1883_;
v___y_1840_ = v_fileName_1879_;
v_toCold_1841_ = v___y_1872_;
v___y_1842_ = v___y_1831_;
goto v___jp_1833_;
}
else
{
uint8_t v___x_1891_; 
lean_inc(v_a_1883_);
v___x_1891_ = l_Lean_MessageData_hasTag(v___y_1871_, v_a_1883_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_dec_ref_known(v___x_1889_, 1);
lean_dec_ref(v___x_1887_);
lean_dec(v_a_1883_);
v___x_1892_ = lean_box(0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1892_);
v___x_1894_ = v___x_1885_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
else
{
lean_del_object(v___x_1885_);
v___y_1834_ = v___y_1873_;
v___y_1835_ = v___x_1890_;
v___y_1836_ = v___y_1874_;
v___y_1837_ = v___x_1889_;
v___y_1838_ = v___x_1887_;
v___y_1839_ = v_a_1883_;
v___y_1840_ = v_fileName_1879_;
v_toCold_1841_ = v___y_1872_;
v___y_1842_ = v___y_1831_;
goto v___jp_1833_;
}
}
}
}
v___jp_1897_:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Syntax_getTailPos_x3f(v___y_1902_, v___y_1903_);
lean_dec(v___y_1902_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_inc(v___y_1904_);
v___y_1871_ = v___y_1898_;
v___y_1872_ = v___y_1899_;
v___y_1873_ = v___y_1901_;
v___y_1874_ = v___y_1903_;
v___y_1875_ = v___y_1904_;
v___y_1876_ = v___y_1900_;
v___y_1877_ = v___y_1899_;
v___y_1878_ = v___y_1904_;
goto v___jp_1870_;
}
else
{
lean_object* v_val_1906_; 
v_val_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_val_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___y_1871_ = v___y_1898_;
v___y_1872_ = v___y_1899_;
v___y_1873_ = v___y_1901_;
v___y_1874_ = v___y_1903_;
v___y_1875_ = v___y_1904_;
v___y_1876_ = v___y_1900_;
v___y_1877_ = v___y_1899_;
v___y_1878_ = v_val_1906_;
goto v___jp_1870_;
}
}
v___jp_1907_:
{
lean_object* v_toCold_1911_; lean_object* v_ref_1912_; uint8_t v_suppressElabErrors_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___f_1916_; lean_object* v_ref_1917_; lean_object* v___x_1918_; 
v_toCold_1911_ = lean_ctor_get(v___y_1830_, 0);
v_ref_1912_ = lean_ctor_get(v___y_1830_, 2);
v_suppressElabErrors_1913_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 2);
v___x_1914_ = lean_box(v_suppressElabErrors_1913_);
v___x_1915_ = lean_box(v___y_1908_);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1916_, 0, v___x_1914_);
lean_closure_set(v___f_1916_, 1, v___x_1915_);
v_ref_1917_ = l_Lean_replaceRef(v_ref_1824_, v_ref_1912_);
v___x_1918_ = l_Lean_Syntax_getPos_x3f(v_ref_1917_, v___y_1909_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___y_1898_ = v___f_1916_;
v___y_1899_ = v_toCold_1911_;
v___y_1900_ = v_suppressElabErrors_1913_;
v___y_1901_ = v___y_1910_;
v___y_1902_ = v_ref_1917_;
v___y_1903_ = v___y_1909_;
v___y_1904_ = v___x_1919_;
goto v___jp_1897_;
}
else
{
lean_object* v_val_1920_; 
v_val_1920_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_val_1920_);
lean_dec_ref_known(v___x_1918_, 1);
v___y_1898_ = v___f_1916_;
v___y_1899_ = v_toCold_1911_;
v___y_1900_ = v_suppressElabErrors_1913_;
v___y_1901_ = v___y_1910_;
v___y_1902_ = v_ref_1917_;
v___y_1903_ = v___y_1909_;
v___y_1904_ = v_val_1920_;
goto v___jp_1897_;
}
}
v___jp_1922_:
{
if (v___y_1925_ == 0)
{
v___y_1908_ = v___y_1923_;
v___y_1909_ = v___y_1924_;
v___y_1910_ = v_severity_1826_;
goto v___jp_1907_;
}
else
{
v___y_1908_ = v___y_1923_;
v___y_1909_ = v___y_1924_;
v___y_1910_ = v___x_1921_;
goto v___jp_1907_;
}
}
v___jp_1926_:
{
if (v___y_1927_ == 0)
{
uint8_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = 1;
v___x_1929_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1826_, v___x_1928_);
if (v___x_1929_ == 0)
{
v___y_1923_ = v___y_1927_;
v___y_1924_ = v___y_1927_;
v___y_1925_ = v___x_1929_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1830_);
v___x_1931_ = l_Lean_warningAsError;
v___x_1932_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v___x_1930_, v___x_1931_);
lean_dec_ref(v___x_1930_);
v___y_1923_ = v___y_1927_;
v___y_1924_ = v___y_1927_;
v___y_1925_ = v___x_1932_;
goto v___jp_1922_;
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec_ref(v_msgData_1825_);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1824_ = stack[0].m_obj;
lean_object* v_msgData_1825_ = stack[1].m_obj;
uint8_t v_severity_1826_ = stack[2].m_num;
uint8_t v_isSilent_1827_ = stack[3].m_num;
lean_object* v___y_1828_ = stack[4].m_obj;
lean_object* v___y_1829_ = stack[5].m_obj;
lean_object* v___y_1830_ = stack[6].m_obj;
lean_object* v___y_1831_ = stack[7].m_obj;
lean_object* v_res_1937_;
v_res_1937_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1824_, v_msgData_1825_, v_severity_1826_, v_isSilent_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
stack->m_obj
 = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1938_, lean_object* v_msgData_1939_, lean_object* v_severity_1940_, lean_object* v_isSilent_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
uint8_t v_severity_boxed_1947_; uint8_t v_isSilent_boxed_1948_; lean_object* v_res_1949_; 
v_severity_boxed_1947_ = lean_unbox(v_severity_1940_);
v_isSilent_boxed_1948_ = lean_unbox(v_isSilent_1941_);
v_res_1949_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1938_, v_msgData_1939_, v_severity_boxed_1947_, v_isSilent_boxed_1948_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v_ref_1938_);
return v_res_1949_;
}
}
lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(lean_object* v_msgData_1950_, uint8_t v_severity_1951_, uint8_t v_isSilent_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_ref_1962_; lean_object* v___x_1963_; 
v_ref_1962_ = lean_ctor_get(v___y_1959_, 2);
v___x_1963_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1962_, v_msgData_1950_, v_severity_1951_, v_isSilent_1952_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1963_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1950_ = stack[0].m_obj;
uint8_t v_severity_1951_ = stack[1].m_num;
uint8_t v_isSilent_1952_ = stack[2].m_num;
lean_object* v___y_1953_ = stack[3].m_obj;
lean_object* v___y_1954_ = stack[4].m_obj;
lean_object* v___y_1955_ = stack[5].m_obj;
lean_object* v___y_1956_ = stack[6].m_obj;
lean_object* v___y_1957_ = stack[7].m_obj;
lean_object* v___y_1958_ = stack[8].m_obj;
lean_object* v___y_1959_ = stack[9].m_obj;
lean_object* v___y_1960_ = stack[10].m_obj;
lean_object* v_res_1964_;
v_res_1964_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1950_, v_severity_1951_, v_isSilent_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
stack->m_obj
 = v_res_1964_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(lean_object* v_msgData_1965_, lean_object* v_severity_1966_, lean_object* v_isSilent_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
uint8_t v_severity_boxed_1977_; uint8_t v_isSilent_boxed_1978_; lean_object* v_res_1979_; 
v_severity_boxed_1977_ = lean_unbox(v_severity_1966_);
v_isSilent_boxed_1978_ = lean_unbox(v_isSilent_1967_);
v_res_1979_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1965_, v_severity_boxed_1977_, v_isSilent_boxed_1978_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1979_;
}
}
lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object* v_msgData_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = 0;
v___x_1991_ = 0;
v___x_1992_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1980_, v___x_1990_, v___x_1991_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1992_;
}
}
LEAN_EXPORT void l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1980_ = stack[0].m_obj;
lean_object* v___y_1981_ = stack[1].m_obj;
lean_object* v___y_1982_ = stack[2].m_obj;
lean_object* v___y_1983_ = stack[3].m_obj;
lean_object* v___y_1984_ = stack[4].m_obj;
lean_object* v___y_1985_ = stack[5].m_obj;
lean_object* v___y_1986_ = stack[6].m_obj;
lean_object* v___y_1987_ = stack[7].m_obj;
lean_object* v___y_1988_ = stack[8].m_obj;
lean_object* v_res_1993_;
v_res_1993_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_msgData_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object* v_msgData_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_msgData_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2004_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* v_ref_2006_, lean_object* v_e_2007_, lean_object* v_origSpan_x3f_2008_, uint8_t v_addSubgoalsMsg_2009_, lean_object* v_codeActionPrefix_x3f_2010_, lean_object* v_checkState_x3f_2011_, uint8_t v_tacticErrorAsInfo_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_2009_, v_checkState_x3f_2011_, v_e_2007_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
if (lean_obj_tag(v_a_2023_) == 0)
{
lean_object* v_val_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_val_2024_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v_a_2023_, 1);
v___x_2025_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_2026_ = 4;
v___x_2027_ = l_Lean_MessageData_nil;
v___x_2028_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2006_, v_val_2024_, v_origSpan_x3f_2008_, v___x_2025_, v_codeActionPrefix_x3f_2010_, v___x_2026_, v___x_2027_, v_a_2019_, v_a_2020_);
return v___x_2028_;
}
else
{
lean_dec(v_codeActionPrefix_x3f_2010_);
lean_dec(v_origSpan_x3f_2008_);
lean_dec(v_ref_2006_);
if (v_tacticErrorAsInfo_2012_ == 0)
{
lean_object* v_val_2029_; lean_object* v___x_2030_; 
v_val_2029_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_val_2029_);
lean_dec_ref_known(v_a_2023_, 1);
v___x_2030_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_2029_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2030_;
}
else
{
lean_object* v_val_2031_; lean_object* v___x_2032_; 
v_val_2031_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_val_2031_);
lean_dec_ref_known(v_a_2023_, 1);
v___x_2032_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_val_2031_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2032_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_codeActionPrefix_x3f_2010_);
lean_dec(v_origSpan_x3f_2008_);
lean_dec(v_ref_2006_);
v_a_2033_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2022_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2022_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addExactSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2006_ = stack[0].m_obj;
lean_object* v_e_2007_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_2008_ = stack[2].m_obj;
uint8_t v_addSubgoalsMsg_2009_ = stack[3].m_num;
lean_object* v_codeActionPrefix_x3f_2010_ = stack[4].m_obj;
lean_object* v_checkState_x3f_2011_ = stack[5].m_obj;
uint8_t v_tacticErrorAsInfo_2012_ = stack[6].m_num;
lean_object* v_a_2013_ = stack[7].m_obj;
lean_object* v_a_2014_ = stack[8].m_obj;
lean_object* v_a_2015_ = stack[9].m_obj;
lean_object* v_a_2016_ = stack[10].m_obj;
lean_object* v_a_2017_ = stack[11].m_obj;
lean_object* v_a_2018_ = stack[12].m_obj;
lean_object* v_a_2019_ = stack[13].m_obj;
lean_object* v_a_2020_ = stack[14].m_obj;
lean_object* v_res_2041_;
v_res_2041_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_ref_2006_, v_e_2007_, v_origSpan_x3f_2008_, v_addSubgoalsMsg_2009_, v_codeActionPrefix_x3f_2010_, v_checkState_x3f_2011_, v_tacticErrorAsInfo_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
stack->m_obj
 = v_res_2041_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* v_ref_2042_, lean_object* v_e_2043_, lean_object* v_origSpan_x3f_2044_, lean_object* v_addSubgoalsMsg_2045_, lean_object* v_codeActionPrefix_x3f_2046_, lean_object* v_checkState_x3f_2047_, lean_object* v_tacticErrorAsInfo_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2058_; uint8_t v_tacticErrorAsInfo_boxed_2059_; lean_object* v_res_2060_; 
v_addSubgoalsMsg_boxed_2058_ = lean_unbox(v_addSubgoalsMsg_2045_);
v_tacticErrorAsInfo_boxed_2059_ = lean_unbox(v_tacticErrorAsInfo_2048_);
v_res_2060_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_ref_2042_, v_e_2043_, v_origSpan_x3f_2044_, v_addSubgoalsMsg_boxed_2058_, v_codeActionPrefix_x3f_2046_, v_checkState_x3f_2047_, v_tacticErrorAsInfo_boxed_2059_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
return v_res_2060_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(lean_object* v_ref_2061_, lean_object* v_msgData_2062_, uint8_t v_severity_2063_, uint8_t v_isSilent_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_2061_, v_msgData_2062_, v_severity_2063_, v_isSilent_2064_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2061_ = stack[0].m_obj;
lean_object* v_msgData_2062_ = stack[1].m_obj;
uint8_t v_severity_2063_ = stack[2].m_num;
uint8_t v_isSilent_2064_ = stack[3].m_num;
lean_object* v___y_2065_ = stack[4].m_obj;
lean_object* v___y_2066_ = stack[5].m_obj;
lean_object* v___y_2067_ = stack[6].m_obj;
lean_object* v___y_2068_ = stack[7].m_obj;
lean_object* v___y_2069_ = stack[8].m_obj;
lean_object* v___y_2070_ = stack[9].m_obj;
lean_object* v___y_2071_ = stack[10].m_obj;
lean_object* v___y_2072_ = stack[11].m_obj;
lean_object* v_res_2075_;
v_res_2075_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_2061_, v_msgData_2062_, v_severity_2063_, v_isSilent_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
stack->m_obj
 = v_res_2075_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2076_, lean_object* v_msgData_2077_, lean_object* v_severity_2078_, lean_object* v_isSilent_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v_severity_boxed_2089_; uint8_t v_isSilent_boxed_2090_; lean_object* v_res_2091_; 
v_severity_boxed_2089_ = lean_unbox(v_severity_2078_);
v_isSilent_boxed_2090_ = lean_unbox(v_isSilent_2079_);
v_res_2091_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_2076_, v_msgData_2077_, v_severity_boxed_2089_, v_isSilent_boxed_2090_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v_ref_2076_);
return v_res_2091_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(uint8_t v_tacticErrorAsInfo_2092_, lean_object* v_as_2093_, size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_b_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_a_2103_; uint8_t v___x_2107_; 
v___x_2107_ = lean_usize_dec_lt(v_i_2095_, v_sz_2094_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_b_2096_);
return v___x_2108_;
}
else
{
lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2135_; 
v_fst_2109_ = lean_ctor_get(v_b_2096_, 0);
v_snd_2110_ = lean_ctor_get(v_b_2096_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_b_2096_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2112_ = v_b_2096_;
v_isShared_2113_ = v_isSharedCheck_2135_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_b_2096_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2135_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_a_2114_; 
v_a_2114_ = lean_array_uget_borrowed(v_as_2093_, v_i_2095_);
if (lean_obj_tag(v_a_2114_) == 0)
{
lean_object* v_val_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v_val_2115_ = lean_ctor_get(v_a_2114_, 0);
lean_inc(v_val_2115_);
v___x_2116_ = lean_array_push(v_fst_2109_, v_val_2115_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2116_);
v___x_2118_ = v___x_2112_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_snd_2110_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
v_a_2103_ = v___x_2118_;
goto v___jp_2102_;
}
}
else
{
lean_object* v_val_2120_; 
v_val_2120_ = lean_ctor_get(v_a_2114_, 0);
if (v_tacticErrorAsInfo_2092_ == 0)
{
lean_object* v___x_2126_; 
lean_inc(v_val_2120_);
v___x_2126_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_2120_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_dec_ref_known(v___x_2126_, 1);
goto v___jp_2121_;
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
goto v___jp_2121_;
}
v___jp_2121_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
lean_inc(v_val_2120_);
v___x_2122_ = lean_array_push(v_snd_2110_, v_val_2120_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2122_);
v___x_2124_ = v___x_2112_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_fst_2109_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
v_a_2103_ = v___x_2124_;
goto v___jp_2102_;
}
}
}
}
}
v___jp_2102_:
{
size_t v___x_2104_; size_t v___x_2105_; 
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2095_, v___x_2104_);
v_i_2095_ = v___x_2105_;
v_b_2096_ = v_a_2103_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_tacticErrorAsInfo_2092_ = stack[0].m_num;
lean_object* v_as_2093_ = stack[1].m_obj;
size_t v_sz_2094_ = stack[2].m_num;
size_t v_i_2095_ = stack[3].m_num;
lean_object* v_b_2096_ = stack[4].m_obj;
lean_object* v___y_2097_ = stack[5].m_obj;
lean_object* v___y_2098_ = stack[6].m_obj;
lean_object* v___y_2099_ = stack[7].m_obj;
lean_object* v___y_2100_ = stack[8].m_obj;
lean_object* v_res_2136_;
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2092_, v_as_2093_, v_sz_2094_, v_i_2095_, v_b_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
stack->m_obj
 = v_res_2136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(lean_object* v_tacticErrorAsInfo_2137_, lean_object* v_as_2138_, lean_object* v_sz_2139_, lean_object* v_i_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2147_; size_t v_sz_boxed_2148_; size_t v_i_boxed_2149_; lean_object* v_res_2150_; 
v_tacticErrorAsInfo_boxed_2147_ = lean_unbox(v_tacticErrorAsInfo_2137_);
v_sz_boxed_2148_ = lean_unbox_usize(v_sz_2139_);
lean_dec(v_sz_2139_);
v_i_boxed_2149_ = lean_unbox_usize(v_i_2140_);
lean_dec(v_i_2140_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_boxed_2147_, v_as_2138_, v_sz_boxed_2148_, v_i_boxed_2149_, v_b_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec_ref(v_as_2138_);
return v_res_2150_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t v_addSubgoalsMsg_2151_, lean_object* v_checkState_x3f_2152_, size_t v_sz_2153_, size_t v_i_2154_, lean_object* v_bs_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_usize_dec_lt(v_i_2154_, v_sz_2153_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_dec(v_checkState_x3f_2152_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_bs_2155_);
return v___x_2166_;
}
else
{
lean_object* v_v_2167_; lean_object* v___x_2168_; lean_object* v_bs_x27_2169_; lean_object* v___x_2170_; 
v_v_2167_ = lean_array_uget(v_bs_2155_, v_i_2154_);
v___x_2168_ = lean_unsigned_to_nat(0u);
v_bs_x27_2169_ = lean_array_uset(v_bs_2155_, v_i_2154_, v___x_2168_);
lean_inc(v_checkState_x3f_2152_);
v___x_2170_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_2151_, v_checkState_x3f_2152_, v_v_2167_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = lean_usize_add(v_i_2154_, v___x_2172_);
v___x_2174_ = lean_array_uset(v_bs_x27_2169_, v_i_2154_, v_a_2171_);
v_i_2154_ = v___x_2173_;
v_bs_2155_ = v___x_2174_;
goto _start;
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_bs_x27_2169_);
lean_dec(v_checkState_x3f_2152_);
v_a_2176_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2170_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2170_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_addSubgoalsMsg_2151_ = stack[0].m_num;
lean_object* v_checkState_x3f_2152_ = stack[1].m_obj;
size_t v_sz_2153_ = stack[2].m_num;
size_t v_i_2154_ = stack[3].m_num;
lean_object* v_bs_2155_ = stack[4].m_obj;
lean_object* v___y_2156_ = stack[5].m_obj;
lean_object* v___y_2157_ = stack[6].m_obj;
lean_object* v___y_2158_ = stack[7].m_obj;
lean_object* v___y_2159_ = stack[8].m_obj;
lean_object* v___y_2160_ = stack[9].m_obj;
lean_object* v___y_2161_ = stack[10].m_obj;
lean_object* v___y_2162_ = stack[11].m_obj;
lean_object* v___y_2163_ = stack[12].m_obj;
lean_object* v_res_2184_;
v_res_2184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_2151_, v_checkState_x3f_2152_, v_sz_2153_, v_i_2154_, v_bs_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
stack->m_obj
 = v_res_2184_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object* v_addSubgoalsMsg_2185_, lean_object* v_checkState_x3f_2186_, lean_object* v_sz_2187_, lean_object* v_i_2188_, lean_object* v_bs_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2199_; size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_addSubgoalsMsg_boxed_2199_ = lean_unbox(v_addSubgoalsMsg_2185_);
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2187_);
lean_dec(v_sz_2187_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2188_);
lean_dec(v_i_2188_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_boxed_2199_, v_checkState_x3f_2186_, v_sz_boxed_2200_, v_i_boxed_2201_, v_bs_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2202_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(lean_object* v_as_2203_, size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_b_2206_);
return v___x_2217_;
}
else
{
lean_object* v___x_2218_; lean_object* v_a_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_box(0);
v_a_2219_ = lean_array_uget_borrowed(v_as_2203_, v_i_2205_);
lean_inc(v_a_2219_);
v___x_2220_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_a_2219_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2220_) == 0)
{
size_t v___x_2221_; size_t v___x_2222_; 
lean_dec_ref_known(v___x_2220_, 1);
v___x_2221_ = ((size_t)1ULL);
v___x_2222_ = lean_usize_add(v_i_2205_, v___x_2221_);
v_i_2205_ = v___x_2222_;
v_b_2206_ = v___x_2218_;
goto _start;
}
else
{
return v___x_2220_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2203_ = stack[0].m_obj;
size_t v_sz_2204_ = stack[1].m_num;
size_t v_i_2205_ = stack[2].m_num;
lean_object* v_b_2206_ = stack[3].m_obj;
lean_object* v___y_2207_ = stack[4].m_obj;
lean_object* v___y_2208_ = stack[5].m_obj;
lean_object* v___y_2209_ = stack[6].m_obj;
lean_object* v___y_2210_ = stack[7].m_obj;
lean_object* v___y_2211_ = stack[8].m_obj;
lean_object* v___y_2212_ = stack[9].m_obj;
lean_object* v___y_2213_ = stack[10].m_obj;
lean_object* v___y_2214_ = stack[11].m_obj;
lean_object* v_res_2224_;
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_2203_, v_sz_2204_, v_i_2205_, v_b_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
stack->m_obj
 = v_res_2224_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(lean_object* v_as_2225_, lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_b_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_2225_, v_sz_boxed_2238_, v_i_boxed_2239_, v_b_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v_as_2225_);
return v_res_2240_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* v_ref_2246_, lean_object* v_es_2247_, lean_object* v_origSpan_x3f_2248_, uint8_t v_addSubgoalsMsg_2249_, lean_object* v_codeActionPrefix_x3f_2250_, lean_object* v_checkState_x3f_2251_, uint8_t v_tacticErrorAsInfo_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
size_t v_sz_2262_; size_t v___x_2263_; lean_object* v___x_2264_; 
v_sz_2262_ = lean_array_size(v_es_2247_);
v___x_2263_ = ((size_t)0ULL);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_2249_, v_checkState_x3f_2251_, v_sz_2262_, v___x_2263_, v_es_2247_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; size_t v_sz_2267_; lean_object* v___x_2268_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1));
v_sz_2267_ = lean_array_size(v_a_2265_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2252_, v_a_2265_, v_sz_2267_, v___x_2263_, v___x_2266_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2265_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v_fst_2270_; lean_object* v_snd_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v_fst_2270_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_fst_2270_);
v_snd_2271_ = lean_ctor_get(v_a_2269_, 1);
lean_inc(v_snd_2271_);
lean_dec(v_a_2269_);
v___x_2272_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2));
v___x_2273_ = 4;
v___x_2274_ = l_Lean_MessageData_nil;
v___x_2275_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2246_, v_fst_2270_, v_origSpan_x3f_2248_, v___x_2272_, v_codeActionPrefix_x3f_2250_, v___x_2273_, v___x_2274_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; size_t v_sz_2277_; lean_object* v___x_2278_; 
lean_dec_ref_known(v___x_2275_, 1);
v___x_2276_ = lean_box(0);
v_sz_2277_ = lean_array_size(v_snd_2271_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_snd_2271_, v_sz_2277_, v___x_2263_, v___x_2276_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_snd_2271_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2278_, 0);
lean_dec(v_unused_2286_);
v___x_2280_ = v___x_2278_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v___x_2278_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2276_);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2276_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
return v___x_2278_;
}
}
else
{
lean_dec(v_snd_2271_);
return v___x_2275_;
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_codeActionPrefix_x3f_2250_);
lean_dec(v_origSpan_x3f_2248_);
lean_dec(v_ref_2246_);
v_a_2287_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2268_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2268_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_codeActionPrefix_x3f_2250_);
lean_dec(v_origSpan_x3f_2248_);
lean_dec(v_ref_2246_);
v_a_2295_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2264_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2264_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addExactSuggestions_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2246_ = stack[0].m_obj;
lean_object* v_es_2247_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_2248_ = stack[2].m_obj;
uint8_t v_addSubgoalsMsg_2249_ = stack[3].m_num;
lean_object* v_codeActionPrefix_x3f_2250_ = stack[4].m_obj;
lean_object* v_checkState_x3f_2251_ = stack[5].m_obj;
uint8_t v_tacticErrorAsInfo_2252_ = stack[6].m_num;
lean_object* v_a_2253_ = stack[7].m_obj;
lean_object* v_a_2254_ = stack[8].m_obj;
lean_object* v_a_2255_ = stack[9].m_obj;
lean_object* v_a_2256_ = stack[10].m_obj;
lean_object* v_a_2257_ = stack[11].m_obj;
lean_object* v_a_2258_ = stack[12].m_obj;
lean_object* v_a_2259_ = stack[13].m_obj;
lean_object* v_a_2260_ = stack[14].m_obj;
lean_object* v_res_2303_;
v_res_2303_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(v_ref_2246_, v_es_2247_, v_origSpan_x3f_2248_, v_addSubgoalsMsg_2249_, v_codeActionPrefix_x3f_2250_, v_checkState_x3f_2251_, v_tacticErrorAsInfo_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
stack->m_obj
 = v_res_2303_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* v_ref_2304_, lean_object* v_es_2305_, lean_object* v_origSpan_x3f_2306_, lean_object* v_addSubgoalsMsg_2307_, lean_object* v_codeActionPrefix_x3f_2308_, lean_object* v_checkState_x3f_2309_, lean_object* v_tacticErrorAsInfo_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2320_; uint8_t v_tacticErrorAsInfo_boxed_2321_; lean_object* v_res_2322_; 
v_addSubgoalsMsg_boxed_2320_ = lean_unbox(v_addSubgoalsMsg_2307_);
v_tacticErrorAsInfo_boxed_2321_ = lean_unbox(v_tacticErrorAsInfo_2310_);
v_res_2322_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(v_ref_2304_, v_es_2305_, v_origSpan_x3f_2306_, v_addSubgoalsMsg_boxed_2320_, v_codeActionPrefix_x3f_2308_, v_checkState_x3f_2309_, v_tacticErrorAsInfo_boxed_2321_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
return v_res_2322_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t v_tacticErrorAsInfo_2323_, lean_object* v_as_2324_, size_t v_sz_2325_, size_t v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2323_, v_as_2324_, v_sz_2325_, v_i_2326_, v_b_2327_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_tacticErrorAsInfo_2323_ = stack[0].m_num;
lean_object* v_as_2324_ = stack[1].m_obj;
size_t v_sz_2325_ = stack[2].m_num;
size_t v_i_2326_ = stack[3].m_num;
lean_object* v_b_2327_ = stack[4].m_obj;
lean_object* v___y_2328_ = stack[5].m_obj;
lean_object* v___y_2329_ = stack[6].m_obj;
lean_object* v___y_2330_ = stack[7].m_obj;
lean_object* v___y_2331_ = stack[8].m_obj;
lean_object* v___y_2332_ = stack[9].m_obj;
lean_object* v___y_2333_ = stack[10].m_obj;
lean_object* v___y_2334_ = stack[11].m_obj;
lean_object* v___y_2335_ = stack[12].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_2323_, v_as_2324_, v_sz_2325_, v_i_2326_, v_b_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object* v_tacticErrorAsInfo_2339_, lean_object* v_as_2340_, lean_object* v_sz_2341_, lean_object* v_i_2342_, lean_object* v_b_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2353_; size_t v_sz_boxed_2354_; size_t v_i_boxed_2355_; lean_object* v_res_2356_; 
v_tacticErrorAsInfo_boxed_2353_ = lean_unbox(v_tacticErrorAsInfo_2339_);
v_sz_boxed_2354_ = lean_unbox_usize(v_sz_2341_);
lean_dec(v_sz_2341_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2342_);
lean_dec(v_i_2342_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_boxed_2353_, v_as_2340_, v_sz_boxed_2354_, v_i_boxed_2355_, v_b_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_as_2340_);
return v_res_2356_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* v_ref_2357_, lean_object* v_e_2358_, lean_object* v_origSpan_x3f_2359_, lean_object* v_header_2360_, lean_object* v_codeActionPrefix_x3f_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_2358_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2369_ = 4;
v___x_2370_ = l_Lean_MessageData_nil;
v___x_2371_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2357_, v_a_2368_, v_origSpan_x3f_2359_, v_header_2360_, v_codeActionPrefix_x3f_2361_, v___x_2369_, v___x_2370_, v_a_2364_, v_a_2365_);
return v___x_2371_;
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_codeActionPrefix_x3f_2361_);
lean_dec_ref(v_header_2360_);
lean_dec(v_origSpan_x3f_2359_);
lean_dec(v_ref_2357_);
v_a_2372_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2367_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2367_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addTermSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2357_ = stack[0].m_obj;
lean_object* v_e_2358_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_2359_ = stack[2].m_obj;
lean_object* v_header_2360_ = stack[3].m_obj;
lean_object* v_codeActionPrefix_x3f_2361_ = stack[4].m_obj;
lean_object* v_a_2362_ = stack[5].m_obj;
lean_object* v_a_2363_ = stack[6].m_obj;
lean_object* v_a_2364_ = stack[7].m_obj;
lean_object* v_a_2365_ = stack[8].m_obj;
lean_object* v_res_2380_;
v_res_2380_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_ref_2357_, v_e_2358_, v_origSpan_x3f_2359_, v_header_2360_, v_codeActionPrefix_x3f_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
stack->m_obj
 = v_res_2380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object* v_ref_2381_, lean_object* v_e_2382_, lean_object* v_origSpan_x3f_2383_, lean_object* v_header_2384_, lean_object* v_codeActionPrefix_x3f_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_ref_2381_, v_e_2382_, v_origSpan_x3f_2383_, v_header_2384_, v_codeActionPrefix_x3f_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
return v_res_2391_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t v_sz_2392_, size_t v_i_2393_, lean_object* v_bs_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_usize_dec_lt(v_i_2393_, v_sz_2392_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_bs_2394_);
return v___x_2401_;
}
else
{
lean_object* v_v_2402_; lean_object* v___x_2403_; lean_object* v_bs_x27_2404_; lean_object* v___x_2405_; 
v_v_2402_ = lean_array_uget(v_bs_2394_, v_i_2393_);
v___x_2403_ = lean_unsigned_to_nat(0u);
v_bs_x27_2404_ = lean_array_uset(v_bs_2394_, v_i_2393_, v___x_2403_);
v___x_2405_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_v_2402_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = ((size_t)1ULL);
v___x_2408_ = lean_usize_add(v_i_2393_, v___x_2407_);
v___x_2409_ = lean_array_uset(v_bs_x27_2404_, v_i_2393_, v_a_2406_);
v_i_2393_ = v___x_2408_;
v_bs_2394_ = v___x_2409_;
goto _start;
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v_bs_x27_2404_);
v_a_2411_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2405_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2405_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2392_ = stack[0].m_num;
size_t v_i_2393_ = stack[1].m_num;
lean_object* v_bs_2394_ = stack[2].m_obj;
lean_object* v___y_2395_ = stack[3].m_obj;
lean_object* v___y_2396_ = stack[4].m_obj;
lean_object* v___y_2397_ = stack[5].m_obj;
lean_object* v___y_2398_ = stack[6].m_obj;
lean_object* v_res_2419_;
v_res_2419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_2392_, v_i_2393_, v_bs_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
stack->m_obj
 = v_res_2419_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object* v_sz_2420_, lean_object* v_i_2421_, lean_object* v_bs_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
size_t v_sz_boxed_2428_; size_t v_i_boxed_2429_; lean_object* v_res_2430_; 
v_sz_boxed_2428_ = lean_unbox_usize(v_sz_2420_);
lean_dec(v_sz_2420_);
v_i_boxed_2429_ = lean_unbox_usize(v_i_2421_);
lean_dec(v_i_2421_);
v_res_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_boxed_2428_, v_i_boxed_2429_, v_bs_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2430_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* v_ref_2431_, lean_object* v_es_2432_, lean_object* v_origSpan_x3f_2433_, lean_object* v_header_2434_, lean_object* v_codeActionPrefix_x3f_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v_sz_2441_ = lean_array_size(v_es_2432_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_2441_, v___x_2442_, v_es_2432_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = 4;
v___x_2446_ = l_Lean_MessageData_nil;
v___x_2447_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2431_, v_a_2444_, v_origSpan_x3f_2433_, v_header_2434_, v_codeActionPrefix_x3f_2435_, v___x_2445_, v___x_2446_, v_a_2438_, v_a_2439_);
return v___x_2447_;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_codeActionPrefix_x3f_2435_);
lean_dec_ref(v_header_2434_);
lean_dec(v_origSpan_x3f_2433_);
lean_dec(v_ref_2431_);
v_a_2448_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2443_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2443_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addTermSuggestions_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2431_ = stack[0].m_obj;
lean_object* v_es_2432_ = stack[1].m_obj;
lean_object* v_origSpan_x3f_2433_ = stack[2].m_obj;
lean_object* v_header_2434_ = stack[3].m_obj;
lean_object* v_codeActionPrefix_x3f_2435_ = stack[4].m_obj;
lean_object* v_a_2436_ = stack[5].m_obj;
lean_object* v_a_2437_ = stack[6].m_obj;
lean_object* v_a_2438_ = stack[7].m_obj;
lean_object* v_a_2439_ = stack[8].m_obj;
lean_object* v_res_2456_;
v_res_2456_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(v_ref_2431_, v_es_2432_, v_origSpan_x3f_2433_, v_header_2434_, v_codeActionPrefix_x3f_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
stack->m_obj
 = v_res_2456_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object* v_ref_2457_, lean_object* v_es_2458_, lean_object* v_origSpan_x3f_2459_, lean_object* v_header_2460_, lean_object* v_codeActionPrefix_x3f_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(v_ref_2457_, v_es_2458_, v_origSpan_x3f_2459_, v_header_2460_, v_codeActionPrefix_x3f_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
return v_res_2467_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Array_mkArray0___redArg();
return v___x_2482_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16));
v___x_2507_ = l_Lean_stringToMessageData(v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21));
v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_2532_ = l_String_toRawSubstring_x27(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80));
v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82));
v___x_2674_ = l_Lean_stringToMessageData(v___x_2673_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84));
v___x_2677_ = l_Lean_stringToMessageData(v___x_2676_);
return v___x_2677_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object* v_e_2678_, lean_object* v_t_x3f_2679_, uint8_t v_a_2680_, lean_object* v_h_x3f_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v___x_2700_; 
lean_inc_ref(v_e_2678_);
v___x_2700_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_2678_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___y_2703_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
if (lean_obj_tag(v_t_x3f_2679_) == 1)
{
lean_object* v_val_2731_; lean_object* v___x_2732_; 
v_val_2731_ = lean_ctor_get(v_t_x3f_2679_, 0);
lean_inc_n(v_val_2731_, 2);
lean_dec_ref_known(v_t_x3f_2679_, 1);
v___x_2732_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_val_2731_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___y_2735_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
if (v_a_2680_ == 0)
{
if (lean_obj_tag(v_h_x3f_2681_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2735_ = v___x_2772_;
goto v___jp_2734_;
}
else
{
lean_object* v_val_2773_; 
v_val_2773_ = lean_ctor_get(v_h_x3f_2681_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v_h_x3f_2681_, 1);
v___y_2735_ = v_val_2773_;
goto v___jp_2734_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2681_) == 0)
{
lean_object* v_toCold_2774_; lean_object* v_ref_2775_; lean_object* v_quotContext_2776_; lean_object* v_currMacroScope_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_toCold_2774_ = lean_ctor_get(v___y_2684_, 0);
v_ref_2775_ = lean_ctor_get(v___y_2684_, 2);
v_quotContext_2776_ = lean_ctor_get(v_toCold_2774_, 8);
v_currMacroScope_2777_ = lean_ctor_get(v_toCold_2774_, 9);
v___x_2778_ = 0;
v___x_2779_ = l_Lean_SourceInfo_fromRef(v_ref_2775_, v___x_2778_);
v___x_2780_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2781_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2779_, 12);
v___x_2782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2779_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2785_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2779_);
lean_ctor_set(v___x_2786_, 1, v___x_2784_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
lean_inc_ref(v___x_2786_);
v___x_2787_ = l_Lean_Syntax_node1(v___x_2779_, v___x_2783_, v___x_2786_);
v___x_2788_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2789_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2790_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2791_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2792_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2793_ = lean_box(0);
lean_inc(v_currMacroScope_2777_);
lean_inc(v_quotContext_2776_);
v___x_2794_ = l_Lean_addMacroScope(v_quotContext_2776_, v___x_2793_, v_currMacroScope_2777_);
v___x_2795_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2796_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2779_);
lean_ctor_set(v___x_2796_, 1, v___x_2792_);
lean_ctor_set(v___x_2796_, 2, v___x_2794_);
lean_ctor_set(v___x_2796_, 3, v___x_2795_);
v___x_2797_ = l_Lean_Syntax_node1(v___x_2779_, v___x_2791_, v___x_2796_);
v___x_2798_ = l_Lean_Syntax_node1(v___x_2779_, v___x_2790_, v___x_2797_);
v___x_2799_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2800_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2779_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_Syntax_node2(v___x_2779_, v___x_2799_, v___x_2801_, v_a_2733_);
v___x_2803_ = l_Lean_Syntax_node1(v___x_2779_, v___x_2784_, v___x_2802_);
v___x_2804_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2779_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_Syntax_node5(v___x_2779_, v___x_2789_, v___x_2798_, v___x_2786_, v___x_2803_, v___x_2805_, v_a_2701_);
v___x_2807_ = l_Lean_Syntax_node1(v___x_2779_, v___x_2788_, v___x_2806_);
v___x_2808_ = l_Lean_Syntax_node3(v___x_2779_, v___x_2780_, v___x_2782_, v___x_2787_, v___x_2807_);
v___x_2809_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81);
v___x_2810_ = l_Lean_MessageData_ofExpr(v_val_2731_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = l_Lean_MessageData_ofExpr(v_e_2678_);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v_fst_2688_ = v___x_2808_;
v_snd_2689_ = v___x_2815_;
goto v___jp_2687_;
}
else
{
lean_object* v_val_2816_; lean_object* v_ref_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_val_2816_ = lean_ctor_get(v_h_x3f_2681_, 0);
lean_inc_n(v_val_2816_, 2);
lean_dec_ref_known(v_h_x3f_2681_, 1);
v_ref_2817_ = lean_ctor_get(v___y_2684_, 2);
v___x_2818_ = 0;
v___x_2819_ = l_Lean_SourceInfo_fromRef(v_ref_2817_, v___x_2818_);
v___x_2820_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2821_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2819_, 10);
v___x_2822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2819_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2825_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2819_);
lean_ctor_set(v___x_2826_, 1, v___x_2824_);
lean_ctor_set(v___x_2826_, 2, v___x_2825_);
lean_inc_ref(v___x_2826_);
v___x_2827_ = l_Lean_Syntax_node1(v___x_2819_, v___x_2823_, v___x_2826_);
v___x_2828_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2829_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2830_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2831_ = l_Lean_mkIdent(v_val_2816_);
v___x_2832_ = l_Lean_Syntax_node1(v___x_2819_, v___x_2830_, v___x_2831_);
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2834_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2819_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_Syntax_node2(v___x_2819_, v___x_2833_, v___x_2835_, v_a_2733_);
v___x_2837_ = l_Lean_Syntax_node1(v___x_2819_, v___x_2824_, v___x_2836_);
v___x_2838_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2819_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = l_Lean_Syntax_node5(v___x_2819_, v___x_2829_, v___x_2832_, v___x_2826_, v___x_2837_, v___x_2839_, v_a_2701_);
v___x_2841_ = l_Lean_Syntax_node1(v___x_2819_, v___x_2828_, v___x_2840_);
v___x_2842_ = l_Lean_Syntax_node3(v___x_2819_, v___x_2820_, v___x_2822_, v___x_2827_, v___x_2841_);
v___x_2843_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2844_ = l_Lean_MessageData_ofName(v_val_2816_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = l_Lean_MessageData_ofExpr(v_val_2731_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_MessageData_ofExpr(v_e_2678_);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v_fst_2688_ = v___x_2842_;
v_snd_2689_ = v___x_2853_;
goto v___jp_2687_;
}
}
v___jp_2734_:
{
lean_object* v_ref_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_ref_2736_ = lean_ctor_get(v___y_2684_, 2);
v___x_2737_ = l_Lean_SourceInfo_fromRef(v_ref_2736_, v_a_2680_);
v___x_2738_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2739_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2737_, 10);
v___x_2740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2737_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2743_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2737_);
lean_ctor_set(v___x_2744_, 1, v___x_2742_);
lean_ctor_set(v___x_2744_, 2, v___x_2743_);
lean_inc_ref(v___x_2744_);
v___x_2745_ = l_Lean_Syntax_node1(v___x_2737_, v___x_2741_, v___x_2744_);
v___x_2746_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2747_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2748_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2735_);
v___x_2749_ = l_Lean_mkIdent(v___y_2735_);
v___x_2750_ = l_Lean_Syntax_node1(v___x_2737_, v___x_2748_, v___x_2749_);
v___x_2751_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2752_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2737_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_Syntax_node2(v___x_2737_, v___x_2751_, v___x_2753_, v_a_2733_);
v___x_2755_ = l_Lean_Syntax_node1(v___x_2737_, v___x_2742_, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2737_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Lean_Syntax_node5(v___x_2737_, v___x_2747_, v___x_2750_, v___x_2744_, v___x_2755_, v___x_2757_, v_a_2701_);
v___x_2759_ = l_Lean_Syntax_node1(v___x_2737_, v___x_2746_, v___x_2758_);
v___x_2760_ = l_Lean_Syntax_node3(v___x_2737_, v___x_2738_, v___x_2740_, v___x_2745_, v___x_2759_);
v___x_2761_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2762_ = l_Lean_MessageData_ofName(v___y_2735_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Lean_MessageData_ofExpr(v_val_2731_);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l_Lean_MessageData_ofExpr(v_e_2678_);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v_fst_2688_ = v___x_2760_;
v_snd_2689_ = v___x_2771_;
goto v___jp_2687_;
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_val_2731_);
lean_dec(v_a_2701_);
lean_dec_ref(v___y_2684_);
lean_dec(v_h_x3f_2681_);
lean_dec_ref(v_e_2678_);
v_a_2854_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2732_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2732_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_dec(v_t_x3f_2679_);
if (v_a_2680_ == 0)
{
if (lean_obj_tag(v_h_x3f_2681_) == 0)
{
lean_object* v___x_2862_; 
v___x_2862_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2703_ = v___x_2862_;
goto v___jp_2702_;
}
else
{
lean_object* v_val_2863_; 
v_val_2863_ = lean_ctor_get(v_h_x3f_2681_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v_h_x3f_2681_, 1);
v___y_2703_ = v_val_2863_;
goto v___jp_2702_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2681_) == 0)
{
lean_object* v_toCold_2864_; lean_object* v_ref_2865_; lean_object* v_quotContext_2866_; lean_object* v_currMacroScope_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_toCold_2864_ = lean_ctor_get(v___y_2684_, 0);
v_ref_2865_ = lean_ctor_get(v___y_2684_, 2);
v_quotContext_2866_ = lean_ctor_get(v_toCold_2864_, 8);
v_currMacroScope_2867_ = lean_ctor_get(v_toCold_2864_, 9);
v___x_2868_ = 0;
v___x_2869_ = l_Lean_SourceInfo_fromRef(v_ref_2865_, v___x_2868_);
v___x_2870_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2871_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2869_, 9);
v___x_2872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2875_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2869_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
lean_ctor_set(v___x_2876_, 2, v___x_2875_);
lean_inc_ref_n(v___x_2876_, 2);
v___x_2877_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2873_, v___x_2876_);
v___x_2878_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2879_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2880_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2881_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2882_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2883_ = lean_box(0);
lean_inc(v_currMacroScope_2867_);
lean_inc(v_quotContext_2866_);
v___x_2884_ = l_Lean_addMacroScope(v_quotContext_2866_, v___x_2883_, v_currMacroScope_2867_);
v___x_2885_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2869_);
lean_ctor_set(v___x_2886_, 1, v___x_2882_);
lean_ctor_set(v___x_2886_, 2, v___x_2884_);
lean_ctor_set(v___x_2886_, 3, v___x_2885_);
v___x_2887_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2881_, v___x_2886_);
v___x_2888_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2880_, v___x_2887_);
v___x_2889_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2869_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = l_Lean_Syntax_node5(v___x_2869_, v___x_2879_, v___x_2888_, v___x_2876_, v___x_2876_, v___x_2890_, v_a_2701_);
v___x_2892_ = l_Lean_Syntax_node1(v___x_2869_, v___x_2878_, v___x_2891_);
v___x_2893_ = l_Lean_Syntax_node3(v___x_2869_, v___x_2870_, v___x_2872_, v___x_2877_, v___x_2892_);
v___x_2894_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85);
v___x_2895_ = l_Lean_MessageData_ofExpr(v_e_2678_);
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v_fst_2688_ = v___x_2893_;
v_snd_2689_ = v___x_2896_;
goto v___jp_2687_;
}
else
{
lean_object* v_val_2897_; lean_object* v_ref_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_val_2897_ = lean_ctor_get(v_h_x3f_2681_, 0);
lean_inc_n(v_val_2897_, 2);
lean_dec_ref_known(v_h_x3f_2681_, 1);
v_ref_2898_ = lean_ctor_get(v___y_2684_, 2);
v___x_2899_ = 0;
v___x_2900_ = l_Lean_SourceInfo_fromRef(v_ref_2898_, v___x_2899_);
v___x_2901_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2902_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2900_, 7);
v___x_2903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2900_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2906_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2900_);
lean_ctor_set(v___x_2907_, 1, v___x_2905_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
lean_inc_ref_n(v___x_2907_, 2);
v___x_2908_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2904_, v___x_2907_);
v___x_2909_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2910_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2911_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2912_ = l_Lean_mkIdent(v_val_2897_);
v___x_2913_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2911_, v___x_2912_);
v___x_2914_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2900_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = l_Lean_Syntax_node5(v___x_2900_, v___x_2910_, v___x_2913_, v___x_2907_, v___x_2907_, v___x_2915_, v_a_2701_);
v___x_2917_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2909_, v___x_2916_);
v___x_2918_ = l_Lean_Syntax_node3(v___x_2900_, v___x_2901_, v___x_2903_, v___x_2908_, v___x_2917_);
v___x_2919_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2920_ = l_Lean_MessageData_ofName(v_val_2897_);
v___x_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = l_Lean_MessageData_ofExpr(v_e_2678_);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v_fst_2688_ = v___x_2918_;
v_snd_2689_ = v___x_2925_;
goto v___jp_2687_;
}
}
}
v___jp_2702_:
{
lean_object* v_ref_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_ref_2704_ = lean_ctor_get(v___y_2684_, 2);
v___x_2705_ = l_Lean_SourceInfo_fromRef(v_ref_2704_, v_a_2680_);
v___x_2706_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2707_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2705_, 7);
v___x_2708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2705_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2711_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2705_);
lean_ctor_set(v___x_2712_, 1, v___x_2710_);
lean_ctor_set(v___x_2712_, 2, v___x_2711_);
lean_inc_ref_n(v___x_2712_, 2);
v___x_2713_ = l_Lean_Syntax_node1(v___x_2705_, v___x_2709_, v___x_2712_);
v___x_2714_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2715_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2716_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2703_);
v___x_2717_ = l_Lean_mkIdent(v___y_2703_);
v___x_2718_ = l_Lean_Syntax_node1(v___x_2705_, v___x_2716_, v___x_2717_);
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2705_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_Syntax_node5(v___x_2705_, v___x_2715_, v___x_2718_, v___x_2712_, v___x_2712_, v___x_2720_, v_a_2701_);
v___x_2722_ = l_Lean_Syntax_node1(v___x_2705_, v___x_2714_, v___x_2721_);
v___x_2723_ = l_Lean_Syntax_node3(v___x_2705_, v___x_2706_, v___x_2708_, v___x_2713_, v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2725_ = l_Lean_MessageData_ofName(v___y_2703_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = l_Lean_MessageData_ofExpr(v_e_2678_);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v_fst_2688_ = v___x_2723_;
v_snd_2689_ = v___x_2730_;
goto v___jp_2687_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v___y_2684_);
lean_dec(v_h_x3f_2681_);
lean_dec(v_t_x3f_2679_);
lean_dec_ref(v_e_2678_);
v_a_2926_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2700_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2700_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
v___jp_2687_:
{
lean_object* v___x_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2699_; 
v___x_2690_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_snd_2689_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec_ref(v___y_2684_);
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_fst_2688_);
lean_ctor_set(v___x_2695_, 1, v_a_2691_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2678_ = stack[0].m_obj;
lean_object* v_t_x3f_2679_ = stack[1].m_obj;
uint8_t v_a_2680_ = stack[2].m_num;
lean_object* v_h_x3f_2681_ = stack[3].m_obj;
lean_object* v___y_2682_ = stack[4].m_obj;
lean_object* v___y_2683_ = stack[5].m_obj;
lean_object* v___y_2684_ = stack[6].m_obj;
lean_object* v___y_2685_ = stack[7].m_obj;
lean_object* v_res_2934_;
v_res_2934_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(v_e_2678_, v_t_x3f_2679_, v_a_2680_, v_h_x3f_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
stack->m_obj
 = v_res_2934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object* v_e_2935_, lean_object* v_t_x3f_2936_, lean_object* v_a_2937_, lean_object* v_h_x3f_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v_a_16927__boxed_2944_; lean_object* v_res_2945_; 
v_a_16927__boxed_2944_ = lean_unbox(v_a_2937_);
v_res_2945_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(v_e_2935_, v_t_x3f_2936_, v_a_16927__boxed_2944_, v_h_x3f_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
return v_res_2945_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1));
v___x_2950_ = l_Lean_MessageData_ofFormat(v___x_2949_);
return v___x_2950_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* v_ref_2951_, lean_object* v_h_x3f_2952_, lean_object* v_t_x3f_2953_, lean_object* v_e_2954_, lean_object* v_origSpan_x3f_2955_, lean_object* v_checkState_x3f_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_tac_2967_; lean_object* v_msg_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___x_2980_; 
lean_inc(v_a_2964_);
lean_inc_ref(v_a_2963_);
lean_inc(v_a_2962_);
lean_inc_ref(v_a_2961_);
lean_inc_ref(v_e_2954_);
v___x_2980_ = lean_infer_type(v_e_2954_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = l_Lean_Meta_isProp(v_a_2981_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2984_, 0, v_e_2954_);
lean_closure_set(v___f_2984_, 1, v_t_x3f_2953_);
lean_closure_set(v___f_2984_, 2, v_a_2983_);
lean_closure_set(v___f_2984_, 3, v_h_x3f_2952_);
v___x_2985_ = l_Lean_Meta_withExposedNames___redArg(v___f_2984_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
if (lean_obj_tag(v_checkState_x3f_2956_) == 1)
{
lean_object* v_fst_2987_; lean_object* v_snd_2988_; lean_object* v_val_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_fst_2987_ = lean_ctor_get(v_a_2986_, 0);
lean_inc(v_fst_2987_);
v_snd_2988_ = lean_ctor_get(v_a_2986_, 1);
lean_inc_n(v_snd_2988_, 2);
lean_dec(v_a_2986_);
v_val_2989_ = lean_ctor_get(v_checkState_x3f_2956_, 0);
lean_inc(v_val_2989_);
lean_dec_ref_known(v_checkState_x3f_2956_, 1);
v___x_2990_ = lean_box(0);
v___x_2991_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_2987_, v_snd_2988_, v_val_2989_, v___x_2990_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
if (lean_obj_tag(v_a_2992_) == 1)
{
lean_object* v_val_2993_; lean_object* v_fst_2994_; lean_object* v_snd_2995_; 
lean_dec(v_snd_2988_);
v_val_2993_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v_a_2992_, 1);
v_fst_2994_ = lean_ctor_get(v_val_2993_, 0);
lean_inc(v_fst_2994_);
v_snd_2995_ = lean_ctor_get(v_val_2993_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_val_2993_);
v_tac_2967_ = v_fst_2994_;
v_msg_2968_ = v_snd_2995_;
v___y_2969_ = v_a_2963_;
v___y_2970_ = v_a_2964_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_a_2992_);
lean_dec(v_origSpan_x3f_2955_);
lean_dec(v_ref_2951_);
v___x_2996_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
v___x_2997_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_2996_, v_snd_2988_);
v___x_2998_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_2997_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3006_; 
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2998_, 0);
lean_dec(v_unused_3007_);
v___x_3000_ = v___x_2998_;
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
else
{
lean_dec(v___x_2998_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = lean_box(0);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3002_);
v___x_3004_ = v___x_3000_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v_snd_2988_);
lean_dec(v_origSpan_x3f_2955_);
lean_dec(v_ref_2951_);
v_a_3008_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2991_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2991_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_fst_3016_; lean_object* v_snd_3017_; 
lean_dec(v_checkState_x3f_2956_);
v_fst_3016_ = lean_ctor_get(v_a_2986_, 0);
lean_inc(v_fst_3016_);
v_snd_3017_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_snd_3017_);
lean_dec(v_a_2986_);
v_tac_2967_ = v_fst_3016_;
v_msg_2968_ = v_snd_3017_;
v___y_2969_ = v_a_2963_;
v___y_2970_ = v_a_2964_;
goto v___jp_2966_;
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_checkState_x3f_2956_);
lean_dec(v_origSpan_x3f_2955_);
lean_dec(v_ref_2951_);
v_a_3018_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2985_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2985_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_checkState_x3f_2956_);
lean_dec(v_origSpan_x3f_2955_);
lean_dec_ref(v_e_2954_);
lean_dec(v_t_x3f_2953_);
lean_dec(v_h_x3f_2952_);
lean_dec(v_ref_2951_);
v_a_3026_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2982_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2982_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_checkState_x3f_2956_);
lean_dec(v_origSpan_x3f_2955_);
lean_dec_ref(v_e_2954_);
lean_dec(v_t_x3f_2953_);
lean_dec(v_h_x3f_2952_);
lean_dec(v_ref_2951_);
v_a_3034_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2980_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2980_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
v___jp_2966_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v_tac_2967_);
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_msg_2968_);
v___x_2975_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2972_);
lean_ctor_set(v___x_2975_, 1, v___x_2973_);
lean_ctor_set(v___x_2975_, 2, v___x_2973_);
lean_ctor_set(v___x_2975_, 3, v___x_2973_);
lean_ctor_set(v___x_2975_, 4, v___x_2974_);
lean_ctor_set(v___x_2975_, 5, v___x_2973_);
v___x_2976_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_2977_ = 4;
v___x_2978_ = l_Lean_MessageData_nil;
v___x_2979_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2951_, v___x_2975_, v_origSpan_x3f_2955_, v___x_2976_, v___x_2973_, v___x_2977_, v___x_2978_, v___y_2969_, v___y_2970_);
return v___x_2979_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addHaveSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2951_ = stack[0].m_obj;
lean_object* v_h_x3f_2952_ = stack[1].m_obj;
lean_object* v_t_x3f_2953_ = stack[2].m_obj;
lean_object* v_e_2954_ = stack[3].m_obj;
lean_object* v_origSpan_x3f_2955_ = stack[4].m_obj;
lean_object* v_checkState_x3f_2956_ = stack[5].m_obj;
lean_object* v_a_2957_ = stack[6].m_obj;
lean_object* v_a_2958_ = stack[7].m_obj;
lean_object* v_a_2959_ = stack[8].m_obj;
lean_object* v_a_2960_ = stack[9].m_obj;
lean_object* v_a_2961_ = stack[10].m_obj;
lean_object* v_a_2962_ = stack[11].m_obj;
lean_object* v_a_2963_ = stack[12].m_obj;
lean_object* v_a_2964_ = stack[13].m_obj;
lean_object* v_res_3042_;
v_res_3042_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(v_ref_2951_, v_h_x3f_2952_, v_t_x3f_2953_, v_e_2954_, v_origSpan_x3f_2955_, v_checkState_x3f_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
stack->m_obj
 = v_res_3042_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object* v_ref_3043_, lean_object* v_h_x3f_3044_, lean_object* v_t_x3f_3045_, lean_object* v_e_3046_, lean_object* v_origSpan_x3f_3047_, lean_object* v_checkState_x3f_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(v_ref_3043_, v_h_x3f_3044_, v_t_x3f_3045_, v_e_3046_, v_origSpan_x3f_3047_, v_checkState_x3f_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
if (lean_obj_tag(v_a_3060_) == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = l_List_reverse___redArg(v_a_3061_);
return v___x_3062_;
}
else
{
lean_object* v_head_3063_; lean_object* v_tail_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3096_; 
v_head_3063_ = lean_ctor_get(v_a_3060_, 0);
v_tail_3064_ = lean_ctor_get(v_a_3060_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_a_3060_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3066_ = v_a_3060_;
v_isShared_3067_ = v_isSharedCheck_3096_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_tail_3064_);
lean_inc(v_head_3063_);
lean_dec(v_a_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3096_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___y_3069_; lean_object* v_fst_3074_; lean_object* v_snd_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3095_; 
v_fst_3074_ = lean_ctor_get(v_head_3063_, 0);
v_snd_3075_ = lean_ctor_get(v_head_3063_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_head_3063_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3077_ = v_head_3063_;
v_isShared_3078_ = v_isSharedCheck_3095_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_snd_3075_);
lean_inc(v_fst_3074_);
lean_dec(v_head_3063_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3095_;
goto v_resetjp_3076_;
}
v___jp_3068_:
{
lean_object* v___x_3071_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v_a_3061_);
lean_ctor_set(v___x_3066_, 0, v___y_3069_);
v___x_3071_ = v___x_3066_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___y_3069_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_a_3061_);
v___x_3071_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
v_a_3060_ = v_tail_3064_;
v_a_3061_ = v___x_3071_;
goto _start;
}
}
v_resetjp_3076_:
{
lean_object* v___y_3080_; uint8_t v___x_3092_; 
v___x_3092_ = lean_unbox(v_snd_3075_);
lean_dec(v_snd_3075_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; 
v___x_3093_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_3080_ = v___x_3093_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3094_; 
v___x_3094_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0));
v___y_3080_ = v___x_3094_;
goto v___jp_3079_;
}
v___jp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
lean_inc_ref(v___y_3080_);
v___x_3081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3080_);
v___x_3082_ = l_Lean_MessageData_ofFormat(v___x_3081_);
v___x_3083_ = l_Lean_Expr_isConst(v_fst_3074_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3084_ = l_Lean_MessageData_ofExpr(v_fst_3074_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 7);
lean_ctor_set(v___x_3077_, 1, v___x_3084_);
lean_ctor_set(v___x_3077_, 0, v___x_3082_);
v___x_3086_ = v___x_3077_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
v___y_3069_ = v___x_3086_;
goto v___jp_3068_;
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = l_Lean_MessageData_ofConst(v_fst_3074_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 7);
lean_ctor_set(v___x_3077_, 1, v___x_3088_);
lean_ctor_set(v___x_3077_, 0, v___x_3082_);
v___x_3090_ = v___x_3077_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
v___y_3069_ = v___x_3090_;
goto v___jp_3068_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t v_sz_3104_, size_t v_i_3105_, lean_object* v_bs_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_usize_dec_lt(v_i_3105_, v_sz_3104_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_bs_3106_);
return v___x_3113_;
}
else
{
lean_object* v_v_3114_; lean_object* v_fst_3115_; lean_object* v_snd_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3160_; 
v_v_3114_ = lean_array_uget(v_bs_3106_, v_i_3105_);
v_fst_3115_ = lean_ctor_get(v_v_3114_, 0);
v_snd_3116_ = lean_ctor_get(v_v_3114_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_v_3114_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3118_ = v_v_3114_;
v_isShared_3119_ = v_isSharedCheck_3160_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_snd_3116_);
lean_inc(v_fst_3115_);
lean_dec(v_v_3114_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3160_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v_bs_x27_3121_; lean_object* v_a_3123_; lean_object* v___x_3128_; 
v___x_3120_ = lean_unsigned_to_nat(0u);
v_bs_x27_3121_ = lean_array_uset(v_bs_3106_, v_i_3105_, v___x_3120_);
v___x_3128_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_fst_3115_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3128_) == 0)
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_unbox(v_snd_3116_);
if (v___x_3129_ == 0)
{
lean_object* v_a_3130_; lean_object* v_ref_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_del_object(v___x_3118_);
v_a_3130_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v___x_3128_, 1);
v_ref_3131_ = lean_ctor_get(v___y_3109_, 2);
v___x_3132_ = lean_unbox(v_snd_3116_);
lean_dec(v_snd_3116_);
v___x_3133_ = l_Lean_SourceInfo_fromRef(v_ref_3131_, v___x_3132_);
v___x_3134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3136_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
lean_inc(v___x_3133_);
v___x_3137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3133_);
lean_ctor_set(v___x_3137_, 1, v___x_3135_);
lean_ctor_set(v___x_3137_, 2, v___x_3136_);
v___x_3138_ = l_Lean_Syntax_node2(v___x_3133_, v___x_3134_, v___x_3137_, v_a_3130_);
v_a_3123_ = v___x_3138_;
goto v___jp_3122_;
}
else
{
lean_object* v_a_3139_; lean_object* v_ref_3140_; uint8_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
lean_dec(v_snd_3116_);
v_a_3139_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3128_, 1);
v_ref_3140_ = lean_ctor_get(v___y_3109_, 2);
v___x_3141_ = 0;
v___x_3142_ = l_Lean_SourceInfo_fromRef(v_ref_3140_, v___x_3141_);
v___x_3143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2));
lean_inc(v___x_3142_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 2);
lean_ctor_set(v___x_3118_, 1, v___x_3145_);
lean_ctor_set(v___x_3118_, 0, v___x_3142_);
v___x_3147_ = v___x_3118_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_inc(v___x_3142_);
v___x_3148_ = l_Lean_Syntax_node1(v___x_3142_, v___x_3144_, v___x_3147_);
v___x_3149_ = l_Lean_Syntax_node2(v___x_3142_, v___x_3143_, v___x_3148_, v_a_3139_);
v_a_3123_ = v___x_3149_;
goto v___jp_3122_;
}
}
}
else
{
lean_del_object(v___x_3118_);
lean_dec(v_snd_3116_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3151_; 
v_a_3151_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3128_, 1);
v_a_3123_ = v_a_3151_;
goto v___jp_3122_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v_bs_x27_3121_);
v_a_3152_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3128_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3128_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
v___jp_3122_:
{
size_t v___x_3124_; size_t v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((size_t)1ULL);
v___x_3125_ = lean_usize_add(v_i_3105_, v___x_3124_);
v___x_3126_ = lean_array_uset(v_bs_x27_3121_, v_i_3105_, v_a_3123_);
v_i_3105_ = v___x_3125_;
v_bs_3106_ = v___x_3126_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3104_ = stack[0].m_num;
size_t v_i_3105_ = stack[1].m_num;
lean_object* v_bs_3106_ = stack[2].m_obj;
lean_object* v___y_3107_ = stack[3].m_obj;
lean_object* v___y_3108_ = stack[4].m_obj;
lean_object* v___y_3109_ = stack[5].m_obj;
lean_object* v___y_3110_ = stack[6].m_obj;
lean_object* v_res_3161_;
v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_3104_, v_i_3105_, v_bs_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
stack->m_obj
 = v_res_3161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object* v_sz_3162_, lean_object* v_i_3163_, lean_object* v_bs_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
size_t v_sz_boxed_3170_; size_t v_i_boxed_3171_; lean_object* v_res_3172_; 
v_sz_boxed_3170_ = lean_unbox_usize(v_sz_3162_);
lean_dec(v_sz_3162_);
v_i_boxed_3171_ = lean_unbox_usize(v_i_3163_);
lean_dec(v_i_3163_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_boxed_3170_, v_i_boxed_3171_, v_bs_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0));
v___x_3175_ = l_Lean_stringToMessageData(v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2));
v___x_3178_ = l_Lean_stringToMessageData(v___x_3177_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6));
v___x_3185_ = l_Lean_MessageData_ofFormat(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object* v_type_x3f_3229_, lean_object* v_rules_3230_, lean_object* v_loc_x3f_3231_, lean_object* v___x_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_extraMsg_3241_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; size_t v_sz_3286_; size_t v___x_3287_; lean_object* v___x_3288_; 
v_sz_3286_ = lean_array_size(v___x_3232_);
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_3286_, v___x_3287_, v___x_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v_a_3293_; lean_object* v_a_3318_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v___x_3290_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12));
v___x_3291_ = l_Lean_Syntax_SepArray_ofElems(v___x_3290_, v_a_3289_);
lean_dec(v_a_3289_);
if (lean_obj_tag(v_loc_x3f_3231_) == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_box(0);
v_a_3293_ = v___x_3320_;
goto v___jp_3292_;
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_val_3321_ = lean_ctor_get(v_loc_x3f_3231_, 0);
v___x_3322_ = lean_box(1);
lean_inc(v_val_3321_);
v___x_3323_ = l_Lean_PrettyPrinter_delab(v_val_3321_, v___x_3322_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v_ref_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v_ref_3325_ = lean_ctor_get(v___y_3235_, 2);
v___x_3326_ = 0;
v___x_3327_ = l_Lean_SourceInfo_fromRef(v_ref_3325_, v___x_3326_);
v___x_3328_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24));
v___x_3329_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25));
lean_inc_n(v___x_3327_, 3);
v___x_3330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3327_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27));
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3333_ = l_Lean_Syntax_node1(v___x_3327_, v___x_3332_, v_a_3324_);
v___x_3334_ = l_Lean_Syntax_node1(v___x_3327_, v___x_3331_, v___x_3333_);
v___x_3335_ = l_Lean_Syntax_node2(v___x_3327_, v___x_3328_, v___x_3330_, v___x_3334_);
v_a_3318_ = v___x_3335_;
goto v___jp_3317_;
}
else
{
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3336_; 
v_a_3336_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3323_, 1);
v_a_3318_ = v_a_3336_;
goto v___jp_3317_;
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref_known(v_loc_x3f_3231_, 1);
lean_dec_ref(v___x_3291_);
lean_dec(v_rules_3230_);
lean_dec(v_type_x3f_3229_);
v_a_3337_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3323_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3323_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
v___jp_3292_:
{
lean_object* v_ref_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_ref_3294_ = lean_ctor_get(v___y_3235_, 2);
v___x_3295_ = 0;
v___x_3296_ = l_Lean_SourceInfo_fromRef(v_ref_3294_, v___x_3295_);
v___x_3297_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14));
v___x_3298_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15));
lean_inc_n(v___x_3296_, 7);
v___x_3299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17));
v___x_3301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3302_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_3303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3296_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
lean_ctor_set(v___x_3303_, 2, v___x_3302_);
v___x_3304_ = l_Lean_Syntax_node1(v___x_3296_, v___x_3300_, v___x_3303_);
v___x_3305_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19));
v___x_3306_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20));
v___x_3307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3296_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Array_append___redArg(v___x_3302_, v___x_3291_);
lean_dec_ref(v___x_3291_);
v___x_3309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3296_);
lean_ctor_set(v___x_3309_, 1, v___x_3301_);
lean_ctor_set(v___x_3309_, 2, v___x_3308_);
v___x_3310_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21));
v___x_3311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3296_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = l_Lean_Syntax_node3(v___x_3296_, v___x_3305_, v___x_3307_, v___x_3309_, v___x_3311_);
if (lean_obj_tag(v_a_3293_) == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___y_3261_ = v___x_3297_;
v___y_3262_ = v___x_3299_;
v___y_3263_ = v___x_3301_;
v___y_3264_ = v___x_3304_;
v___y_3265_ = v___x_3296_;
v___y_3266_ = v___x_3302_;
v___y_3267_ = v___x_3312_;
v___y_3268_ = v___x_3313_;
goto v___jp_3260_;
}
else
{
lean_object* v_val_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_val_3314_ = lean_ctor_get(v_a_3293_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v_a_3293_, 1);
v___x_3315_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___x_3316_ = lean_array_push(v___x_3315_, v_val_3314_);
v___y_3261_ = v___x_3297_;
v___y_3262_ = v___x_3299_;
v___y_3263_ = v___x_3301_;
v___y_3264_ = v___x_3304_;
v___y_3265_ = v___x_3296_;
v___y_3266_ = v___x_3302_;
v___y_3267_ = v___x_3312_;
v___y_3268_ = v___x_3316_;
goto v___jp_3260_;
}
}
v___jp_3317_:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_a_3318_);
v_a_3293_ = v___x_3319_;
goto v___jp_3292_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_loc_x3f_3231_);
lean_dec(v_rules_3230_);
lean_dec(v_type_x3f_3229_);
v_a_3345_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3288_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3288_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
v___jp_3238_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___y_3240_);
lean_ctor_set(v___x_3242_, 1, v_extraMsg_3241_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___y_3239_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
v___jp_3245_:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___y_3247_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
switch(lean_obj_tag(v_type_x3f_3229_))
{
case 0:
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1);
v___y_3239_ = v___y_3246_;
v___y_3240_ = v_a_3249_;
v_extraMsg_3241_ = v___x_3250_;
goto v___jp_3238_;
}
case 1:
{
lean_object* v_a_3251_; lean_object* v_a_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v_a_3257_; 
v_a_3251_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___x_3248_);
v_a_3252_ = lean_ctor_get(v_type_x3f_3229_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v_type_x3f_3229_, 1);
v___x_3253_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3);
v___x_3254_ = l_Lean_MessageData_ofExpr(v_a_3252_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_3255_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3256_);
v___y_3239_ = v___y_3246_;
v___y_3240_ = v_a_3251_;
v_extraMsg_3241_ = v_a_3257_;
goto v___jp_3238_;
}
default: 
{
lean_object* v_a_3258_; lean_object* v___x_3259_; 
v_a_3258_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3258_);
lean_dec_ref(v___x_3248_);
v___x_3259_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4);
v___y_3239_ = v___y_3246_;
v___y_3240_ = v_a_3258_;
v_extraMsg_3241_ = v___x_3259_;
goto v___jp_3238_;
}
}
}
v___jp_3260_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3269_ = l_Array_append___redArg(v___y_3266_, v___y_3268_);
lean_dec_ref(v___y_3268_);
lean_inc(v___y_3263_);
lean_inc(v___y_3265_);
v___x_3270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3270_, 0, v___y_3265_);
lean_ctor_set(v___x_3270_, 1, v___y_3263_);
lean_ctor_set(v___x_3270_, 2, v___x_3269_);
lean_inc(v___y_3261_);
v___x_3271_ = l_Lean_Syntax_node4(v___y_3265_, v___y_3261_, v___y_3262_, v___y_3264_, v___y_3267_, v___x_3270_);
v___x_3272_ = lean_box(0);
v___x_3273_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(v_rules_3230_, v___x_3272_);
v___x_3274_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7);
v___x_3275_ = l_Lean_MessageData_joinSep(v___x_3273_, v___x_3274_);
v___x_3276_ = l_Lean_MessageData_sbracket(v___x_3275_);
if (lean_obj_tag(v_loc_x3f_3231_) == 1)
{
lean_object* v_val_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_val_3277_ = lean_ctor_get(v_loc_x3f_3231_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v_loc_x3f_3231_, 1);
v___x_3278_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3276_);
v___x_3280_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_MessageData_ofExpr(v_val_3277_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___y_3246_ = v___x_3271_;
v___y_3247_ = v___x_3283_;
goto v___jp_3245_;
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_loc_x3f_3231_);
v___x_3284_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___x_3276_);
v___y_3246_ = v___x_3271_;
v___y_3247_ = v___x_3285_;
goto v___jp_3245_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_x3f_3229_ = stack[0].m_obj;
lean_object* v_rules_3230_ = stack[1].m_obj;
lean_object* v_loc_x3f_3231_ = stack[2].m_obj;
lean_object* v___x_3232_ = stack[3].m_obj;
lean_object* v___y_3233_ = stack[4].m_obj;
lean_object* v___y_3234_ = stack[5].m_obj;
lean_object* v___y_3235_ = stack[6].m_obj;
lean_object* v___y_3236_ = stack[7].m_obj;
lean_object* v_res_3353_;
v_res_3353_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(v_type_x3f_3229_, v_rules_3230_, v_loc_x3f_3231_, v___x_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
stack->m_obj
 = v_res_3353_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(lean_object* v_type_x3f_3354_, lean_object* v_rules_3355_, lean_object* v_loc_x3f_3356_, lean_object* v___x_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(v_type_x3f_3354_, v_rules_3355_, v_loc_x3f_3356_, v___x_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
return v_res_3363_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1));
v___x_3368_ = l_Lean_MessageData_ofFormat(v___x_3367_);
return v___x_3368_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* v_ref_3369_, lean_object* v_rules_3370_, lean_object* v_type_x3f_3371_, lean_object* v_loc_x3f_3372_, lean_object* v_origSpan_x3f_3373_, lean_object* v_checkState_x3f_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; 
lean_inc(v_rules_3370_);
v___x_3384_ = lean_array_mk(v_rules_3370_);
lean_inc(v_type_x3f_3371_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3385_, 0, v_type_x3f_3371_);
lean_closure_set(v___f_3385_, 1, v_rules_3370_);
lean_closure_set(v___f_3385_, 2, v_loc_x3f_3372_);
lean_closure_set(v___f_3385_, 3, v___x_3384_);
v___x_3386_ = l_Lean_Meta_withExposedNames___redArg(v___f_3385_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v_snd_3388_; lean_object* v_fst_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3460_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v_snd_3388_ = lean_ctor_get(v_a_3387_, 1);
v_fst_3389_ = lean_ctor_get(v_a_3387_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_a_3387_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3391_ = v_a_3387_;
v_isShared_3392_ = v_isSharedCheck_3460_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_snd_3388_);
lean_inc(v_fst_3389_);
lean_dec(v_a_3387_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3460_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_fst_3393_; lean_object* v_snd_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3459_; 
v_fst_3393_ = lean_ctor_get(v_snd_3388_, 0);
v_snd_3394_ = lean_ctor_get(v_snd_3388_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_snd_3388_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3396_ = v_snd_3388_;
v_isShared_3397_ = v_isSharedCheck_3459_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3393_);
lean_dec(v_snd_3388_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3459_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_tac_3399_; lean_object* v_tacMsg_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; 
if (lean_obj_tag(v_checkState_x3f_3374_) == 1)
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3458_; 
v_val_3417_ = lean_ctor_get(v_checkState_x3f_3374_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_checkState_x3f_3374_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3419_ = v_checkState_x3f_3374_;
v_isShared_3420_ = v_isSharedCheck_3458_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v_checkState_x3f_3374_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3458_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___y_3422_; 
if (lean_obj_tag(v_type_x3f_3371_) == 1)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; 
v_a_3453_ = lean_ctor_get(v_type_x3f_3371_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v_type_x3f_3371_, 1);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_a_3453_);
v___x_3455_ = v___x_3419_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
v___y_3422_ = v___x_3455_;
goto v___jp_3421_;
}
}
else
{
lean_object* v___x_3457_; 
lean_del_object(v___x_3419_);
lean_dec(v_type_x3f_3371_);
v___x_3457_ = lean_box(0);
v___y_3422_ = v___x_3457_;
goto v___jp_3421_;
}
v___jp_3421_:
{
lean_object* v___x_3423_; 
lean_inc(v_fst_3393_);
v___x_3423_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_3389_, v_fst_3393_, v_val_3417_, v___y_3422_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
if (lean_obj_tag(v_a_3424_) == 1)
{
lean_object* v_val_3425_; lean_object* v_fst_3426_; lean_object* v_snd_3427_; 
lean_dec(v_fst_3393_);
v_val_3425_ = lean_ctor_get(v_a_3424_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v_a_3424_, 1);
v_fst_3426_ = lean_ctor_get(v_val_3425_, 0);
lean_inc(v_fst_3426_);
v_snd_3427_ = lean_ctor_get(v_val_3425_, 1);
lean_inc(v_snd_3427_);
lean_dec(v_val_3425_);
v_tac_3399_ = v_fst_3426_;
v_tacMsg_3400_ = v_snd_3427_;
v___y_3401_ = v_a_3381_;
v___y_3402_ = v_a_3382_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec(v_a_3424_);
lean_del_object(v___x_3396_);
lean_del_object(v___x_3391_);
lean_dec(v_origSpan_x3f_3373_);
lean_dec(v_ref_3369_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v_fst_3393_);
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v_snd_3394_);
v___x_3434_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_3432_, v___x_3433_);
v___x_3435_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_3434_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3443_; 
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; 
v_unused_3444_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3444_);
v___x_3437_ = v___x_3435_;
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
else
{
lean_dec(v___x_3435_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = lean_box(0);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3439_);
v___x_3441_ = v___x_3437_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
else
{
return v___x_3435_;
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3391_);
lean_dec(v_origSpan_x3f_3373_);
lean_dec(v_ref_3369_);
v_a_3445_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3423_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3423_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
}
else
{
lean_dec(v_checkState_x3f_3374_);
lean_dec(v_type_x3f_3371_);
v_tac_3399_ = v_fst_3389_;
v_tacMsg_3400_ = v_fst_3393_;
v___y_3401_ = v_a_3381_;
v___y_3402_ = v_a_3382_;
goto v___jp_3398_;
}
v___jp_3398_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_tac_3399_);
lean_ctor_set(v___x_3396_, 0, v___x_3403_);
v___x_3405_ = v___x_3396_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_tac_3399_);
v___x_3405_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3406_ = lean_box(0);
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 7);
lean_ctor_set(v___x_3391_, 1, v_snd_3394_);
lean_ctor_set(v___x_3391_, 0, v_tacMsg_3400_);
v___x_3408_ = v___x_3391_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_tacMsg_3400_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_snd_3394_);
v___x_3408_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3405_);
lean_ctor_set(v___x_3410_, 1, v___x_3406_);
lean_ctor_set(v___x_3410_, 2, v___x_3406_);
lean_ctor_set(v___x_3410_, 3, v___x_3406_);
lean_ctor_set(v___x_3410_, 4, v___x_3409_);
lean_ctor_set(v___x_3410_, 5, v___x_3406_);
v___x_3411_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_3412_ = 4;
v___x_3413_ = l_Lean_MessageData_nil;
v___x_3414_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3369_, v___x_3410_, v_origSpan_x3f_3373_, v___x_3411_, v___x_3406_, v___x_3412_, v___x_3413_, v___y_3401_, v___y_3402_);
return v___x_3414_;
}
}
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_checkState_x3f_3374_);
lean_dec(v_origSpan_x3f_3373_);
lean_dec(v_type_x3f_3371_);
lean_dec(v_ref_3369_);
v_a_3461_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3386_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3386_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3369_ = stack[0].m_obj;
lean_object* v_rules_3370_ = stack[1].m_obj;
lean_object* v_type_x3f_3371_ = stack[2].m_obj;
lean_object* v_loc_x3f_3372_ = stack[3].m_obj;
lean_object* v_origSpan_x3f_3373_ = stack[4].m_obj;
lean_object* v_checkState_x3f_3374_ = stack[5].m_obj;
lean_object* v_a_3375_ = stack[6].m_obj;
lean_object* v_a_3376_ = stack[7].m_obj;
lean_object* v_a_3377_ = stack[8].m_obj;
lean_object* v_a_3378_ = stack[9].m_obj;
lean_object* v_a_3379_ = stack[10].m_obj;
lean_object* v_a_3380_ = stack[11].m_obj;
lean_object* v_a_3381_ = stack[12].m_obj;
lean_object* v_a_3382_ = stack[13].m_obj;
lean_object* v_res_3469_;
v_res_3469_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3369_, v_rules_3370_, v_type_x3f_3371_, v_loc_x3f_3372_, v_origSpan_x3f_3373_, v_checkState_x3f_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
stack->m_obj
 = v_res_3469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object* v_ref_3470_, lean_object* v_rules_3471_, lean_object* v_type_x3f_3472_, lean_object* v_loc_x3f_3473_, lean_object* v_origSpan_x3f_3474_, lean_object* v_checkState_x3f_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3470_, v_rules_3471_, v_type_x3f_3472_, v_loc_x3f_3473_, v_origSpan_x3f_3474_, v_checkState_x3f_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
return v_res_3485_;
}
}
lean_object* runtime_initialize_Lean_Server_CodeActions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_CodeActions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_ExposeNames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_CodeActions(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_CodeActions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_TryThis(builtin);
}
#ifdef __cplusplus
}
#endif
