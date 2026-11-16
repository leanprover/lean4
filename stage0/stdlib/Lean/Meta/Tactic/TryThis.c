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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__4));
v___x_12_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v___x_13_ = l_Lean_Widget_addBuiltinModule(v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1(){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___closed__1));
v___x_24_ = l_Lean_Meta_Hint_textInsertionWidget;
v___x_25_ = l_Lean_Widget_addBuiltinModule(v___x_23_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1___boxed(lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Hint_textInsertionWidget___regBuiltin_Lean_Meta_Hint_textInsertionWidget__1();
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(lean_object* v___y_28_){
_start:
{
lean_object* v_doc_30_; lean_object* v___x_31_; 
v_doc_30_ = lean_ctor_get(v___y_28_, 1);
lean_inc_ref(v_doc_30_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v_doc_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___boxed(lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v___y_32_);
lean_dec_ref(v___y_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(lean_object* v___x_38_, lean_object* v_a_39_, lean_object* v_params_40_, lean_object* v___ctx_41_, lean_object* v_info_42_, lean_object* v_result_43_){
_start:
{
if (lean_obj_tag(v_info_42_) == 10)
{
lean_object* v_i_44_; lean_object* v_stx_45_; lean_object* v_value_46_; lean_object* v___x_47_; 
v_i_44_ = lean_ctor_get(v_info_42_, 0);
v_stx_45_ = lean_ctor_get(v_i_44_, 0);
v_value_46_ = lean_ctor_get(v_i_44_, 1);
v___x_47_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_46_, v___x_38_);
if (lean_obj_tag(v___x_47_) == 1)
{
lean_object* v_val_48_; lean_object* v_edit_49_; lean_object* v_codeActionTitle_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
v_val_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v___x_47_, 1);
v_edit_49_ = lean_ctor_get(v_val_48_, 0);
lean_inc_ref(v_edit_49_);
v_codeActionTitle_50_ = lean_ctor_get(v_val_48_, 1);
lean_inc_ref(v_codeActionTitle_50_);
lean_dec(v_val_48_);
v___x_51_ = 0;
v___x_52_ = l_Lean_Syntax_getRange_x3f(v_stx_45_, v___x_51_);
if (lean_obj_tag(v___x_52_) == 1)
{
lean_object* v_toEditableDocumentCore_53_; lean_object* v_meta_54_; lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_89_; 
v_toEditableDocumentCore_53_ = lean_ctor_get(v_a_39_, 0);
v_meta_54_ = lean_ctor_get(v_toEditableDocumentCore_53_, 0);
v_val_55_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_89_ == 0)
{
v___x_57_ = v___x_52_;
v_isShared_58_ = v_isSharedCheck_89_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v___x_52_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_89_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_text_59_; lean_object* v___x_60_; lean_object* v_start_61_; lean_object* v_range_62_; lean_object* v_end_63_; lean_object* v_end_64_; lean_object* v_line_65_; lean_object* v_start_66_; lean_object* v_line_67_; uint8_t v___x_68_; 
v_text_59_ = lean_ctor_get(v_meta_54_, 3);
lean_inc_ref(v_text_59_);
v___x_60_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_59_, v_val_55_);
v_start_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_start_61_);
v_range_62_ = lean_ctor_get(v_params_40_, 3);
v_end_63_ = lean_ctor_get(v_range_62_, 1);
v_end_64_ = lean_ctor_get(v___x_60_, 1);
lean_inc_ref(v_end_64_);
lean_dec_ref(v___x_60_);
v_line_65_ = lean_ctor_get(v_start_61_, 0);
lean_inc(v_line_65_);
lean_dec_ref(v_start_61_);
v_start_66_ = lean_ctor_get(v_range_62_, 0);
v_line_67_ = lean_ctor_get(v_end_63_, 0);
v___x_68_ = lean_nat_dec_le(v_line_65_, v_line_67_);
lean_dec(v_line_65_);
if (v___x_68_ == 0)
{
lean_dec_ref(v_end_64_);
lean_del_object(v___x_57_);
lean_dec_ref(v_codeActionTitle_50_);
lean_dec_ref(v_edit_49_);
lean_dec_ref(v_a_39_);
return v_result_43_;
}
else
{
lean_object* v_line_69_; lean_object* v_line_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_87_; 
v_line_69_ = lean_ctor_get(v_start_66_, 0);
v_line_70_ = lean_ctor_get(v_end_64_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v_end_64_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v_end_64_, 1);
lean_dec(v_unused_88_);
v___x_72_ = v_end_64_;
v_isShared_73_ = v_isSharedCheck_87_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_line_70_);
lean_dec(v_end_64_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_87_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_le(v_line_69_, v_line_70_);
lean_dec(v_line_70_);
if (v___x_74_ == 0)
{
lean_del_object(v___x_72_);
lean_del_object(v___x_57_);
lean_dec_ref(v_codeActionTitle_50_);
lean_dec_ref(v_edit_49_);
lean_dec_ref(v_a_39_);
return v_result_43_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___closed__1));
v___x_77_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_a_39_);
v___x_78_ = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(v___x_77_, v_edit_49_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_78_);
v___x_80_ = v___x_57_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_86_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_81_, 0, v___x_75_);
lean_ctor_set(v___x_81_, 1, v___x_75_);
lean_ctor_set(v___x_81_, 2, v_codeActionTitle_50_);
lean_ctor_set(v___x_81_, 3, v___x_76_);
lean_ctor_set(v___x_81_, 4, v___x_75_);
lean_ctor_set(v___x_81_, 5, v___x_75_);
lean_ctor_set(v___x_81_, 6, v___x_75_);
lean_ctor_set(v___x_81_, 7, v___x_80_);
lean_ctor_set(v___x_81_, 8, v___x_75_);
lean_ctor_set(v___x_81_, 9, v___x_75_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_75_);
lean_ctor_set(v___x_72_, 0, v___x_81_);
v___x_83_ = v___x_72_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_75_);
v___x_83_ = v_reuseFailAlloc_85_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; 
v___x_84_ = lean_array_push(v_result_43_, v___x_83_);
return v___x_84_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_52_);
lean_dec_ref(v_codeActionTitle_50_);
lean_dec_ref(v_edit_49_);
lean_dec_ref(v_a_39_);
return v_result_43_;
}
}
else
{
lean_dec(v___x_47_);
lean_dec_ref(v_a_39_);
return v_result_43_;
}
}
else
{
lean_dec_ref(v_a_39_);
return v_result_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed(lean_object* v___x_90_, lean_object* v_a_91_, lean_object* v_params_92_, lean_object* v___ctx_93_, lean_object* v_info_94_, lean_object* v_result_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(v___x_90_, v_a_91_, v_params_92_, v___ctx_93_, v_info_94_, v_result_95_);
lean_dec_ref(v_info_94_);
lean_dec_ref(v___ctx_93_);
lean_dec_ref(v_params_92_);
lean_dec(v___x_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object* v_params_99_, lean_object* v_snap_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_116_; 
v___x_103_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
v___x_104_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v_a_101_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_116_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_116_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_116_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___f_109_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed), 6, 3);
lean_closure_set(v___f_109_, 0, v___x_103_);
lean_closure_set(v___f_109_, 1, v_a_105_);
lean_closure_set(v___f_109_, 2, v_params_99_);
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0));
v___x_111_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_100_);
v___x_112_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_109_, v___x_110_, v___x_111_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_112_);
v___x_114_ = v___x_107_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object* v_params_117_, lean_object* v_snap_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider(v_params_117_, v_snap_118_, v_a_119_);
lean_dec_ref(v_a_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1(){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__14));
v___x_161_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___boxed), 4, 0);
v___x_162_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(lean_object* v_opts_165_, lean_object* v_opt_166_){
_start:
{
lean_object* v_name_167_; lean_object* v_defValue_168_; lean_object* v_map_169_; lean_object* v___x_170_; 
v_name_167_ = lean_ctor_get(v_opt_166_, 0);
v_defValue_168_ = lean_ctor_get(v_opt_166_, 1);
v_map_169_ = lean_ctor_get(v_opts_165_, 0);
v___x_170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_169_, v_name_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_inc(v_defValue_168_);
return v_defValue_168_;
}
else
{
lean_object* v_val_171_; 
v_val_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v___x_170_, 1);
if (lean_obj_tag(v_val_171_) == 3)
{
lean_object* v_v_172_; 
v_v_172_ = lean_ctor_get(v_val_171_, 0);
lean_inc(v_v_172_);
lean_dec_ref_known(v_val_171_, 1);
return v_v_172_;
}
else
{
lean_dec(v_val_171_);
lean_inc(v_defValue_168_);
return v_defValue_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0___boxed(lean_object* v_opts_173_, lean_object* v_opt_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_opts_173_, v_opt_174_);
lean_dec_ref(v_opt_174_);
lean_dec_ref(v_opts_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(lean_object* v_o_179_, lean_object* v_k_180_, uint8_t v_v_181_){
_start:
{
lean_object* v_map_182_; uint8_t v_hasTrace_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_197_; 
v_map_182_ = lean_ctor_get(v_o_179_, 0);
v_hasTrace_183_ = lean_ctor_get_uint8(v_o_179_, sizeof(void*)*1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_o_179_);
if (v_isSharedCheck_197_ == 0)
{
v___x_185_ = v_o_179_;
v_isShared_186_ = v_isSharedCheck_197_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_map_182_);
lean_dec(v_o_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_197_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_187_, 0, v_v_181_);
lean_inc(v_k_180_);
v___x_188_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_180_, v___x_187_, v_map_182_);
if (v_hasTrace_183_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_192_; 
v___x_189_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__1));
v___x_190_ = l_Lean_Name_isPrefixOf(v___x_189_, v_k_180_);
lean_dec(v_k_180_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_188_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_190_);
return v___x_192_;
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_k_180_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_195_ = v___x_185_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_196_, sizeof(void*)*1, v_hasTrace_183_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___boxed(lean_object* v_o_198_, lean_object* v_k_199_, lean_object* v_v_200_){
_start:
{
uint8_t v_v_boxed_201_; lean_object* v_res_202_; 
v_v_boxed_201_ = lean_unbox(v_v_200_);
v_res_202_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(v_o_198_, v_k_199_, v_v_boxed_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(lean_object* v_opts_203_, lean_object* v_opt_204_, uint8_t v_val_205_){
_start:
{
lean_object* v_name_206_; lean_object* v___x_207_; 
v_name_206_ = lean_ctor_get(v_opt_204_, 0);
lean_inc(v_name_206_);
lean_dec_ref(v_opt_204_);
v___x_207_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1(v_opts_203_, v_name_206_, v_val_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1___boxed(lean_object* v_opts_208_, lean_object* v_opt_209_, lean_object* v_val_210_){
_start:
{
uint8_t v_val_boxed_211_; lean_object* v_res_212_; 
v_val_boxed_211_ = lean_unbox(v_val_210_);
v_res_212_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_opts_208_, v_opt_209_, v_val_boxed_211_);
return v_res_212_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object* v_e_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_toCold_224_; lean_object* v_currRecDepth_225_; lean_object* v_ref_226_; uint8_t v_suppressElabErrors_227_; uint8_t v_checkDeprecated_228_; uint8_t v_isRecordingDeps_229_; lean_object* v_fileName_230_; lean_object* v_fileMap_231_; lean_object* v_options_232_; lean_object* v_currNamespace_233_; lean_object* v_openDecls_234_; lean_object* v_initHeartbeats_235_; lean_object* v_maxHeartbeats_236_; lean_object* v_quotContext_237_; lean_object* v_currMacroScope_238_; lean_object* v_cancelTk_x3f_239_; lean_object* v_inheritedTraceOptions_240_; lean_object* v___x_241_; uint16_t v___y_243_; lean_object* v___y_244_; lean_object* v_fileName_245_; lean_object* v_fileMap_246_; lean_object* v_currNamespace_247_; lean_object* v_openDecls_248_; lean_object* v_initHeartbeats_249_; lean_object* v_maxHeartbeats_250_; lean_object* v_quotContext_251_; lean_object* v_currMacroScope_252_; lean_object* v_cancelTk_x3f_253_; lean_object* v_inheritedTraceOptions_254_; lean_object* v_currRecDepth_255_; lean_object* v_ref_256_; uint8_t v_suppressElabErrors_257_; uint8_t v_checkDeprecated_258_; uint8_t v_isRecordingDeps_259_; lean_object* v___y_260_; uint16_t v___y_267_; lean_object* v___y_268_; uint8_t v___y_269_; lean_object* v___y_292_; 
v_toCold_224_ = lean_ctor_get(v_a_221_, 0);
v_currRecDepth_225_ = lean_ctor_get(v_a_221_, 1);
v_ref_226_ = lean_ctor_get(v_a_221_, 2);
v_suppressElabErrors_227_ = lean_ctor_get_uint8(v_a_221_, sizeof(void*)*3 + 2);
v_checkDeprecated_228_ = lean_ctor_get_uint8(v_a_221_, sizeof(void*)*3 + 3);
v_isRecordingDeps_229_ = lean_ctor_get_uint8(v_a_221_, sizeof(void*)*3 + 4);
v_fileName_230_ = lean_ctor_get(v_toCold_224_, 0);
v_fileMap_231_ = lean_ctor_get(v_toCold_224_, 1);
v_options_232_ = lean_ctor_get(v_toCold_224_, 2);
v_currNamespace_233_ = lean_ctor_get(v_toCold_224_, 4);
v_openDecls_234_ = lean_ctor_get(v_toCold_224_, 5);
v_initHeartbeats_235_ = lean_ctor_get(v_toCold_224_, 6);
v_maxHeartbeats_236_ = lean_ctor_get(v_toCold_224_, 7);
v_quotContext_237_ = lean_ctor_get(v_toCold_224_, 8);
v_currMacroScope_238_ = lean_ctor_get(v_toCold_224_, 9);
v_cancelTk_x3f_239_ = lean_ctor_get(v_toCold_224_, 10);
v_inheritedTraceOptions_240_ = lean_ctor_get(v_toCold_224_, 11);
v___x_241_ = lean_box(1);
if (v_isRecordingDeps_229_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = l_Lean_pp_mvars_anonymous;
lean_inc_ref(v_options_232_);
v___x_304_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_232_, v___x_303_, v_isRecordingDeps_229_);
v___y_292_ = v___x_304_;
goto v___jp_291_;
}
else
{
lean_object* v___x_305_; 
lean_inc_ref(v_options_232_);
v___x_305_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_232_);
v___y_292_ = v___x_305_;
goto v___jp_291_;
}
v___jp_242_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_261_ = l_Lean_maxRecDepth;
v___x_262_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v___y_244_, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_263_, 0, v_fileName_245_);
lean_ctor_set(v___x_263_, 1, v_fileMap_246_);
lean_ctor_set(v___x_263_, 2, v___y_244_);
lean_ctor_set(v___x_263_, 3, v___x_262_);
lean_ctor_set(v___x_263_, 4, v_currNamespace_247_);
lean_ctor_set(v___x_263_, 5, v_openDecls_248_);
lean_ctor_set(v___x_263_, 6, v_initHeartbeats_249_);
lean_ctor_set(v___x_263_, 7, v_maxHeartbeats_250_);
lean_ctor_set(v___x_263_, 8, v_quotContext_251_);
lean_ctor_set(v___x_263_, 9, v_currMacroScope_252_);
lean_ctor_set(v___x_263_, 10, v_cancelTk_x3f_253_);
lean_ctor_set(v___x_263_, 11, v_inheritedTraceOptions_254_);
lean_inc(v_ref_256_);
lean_inc(v_currRecDepth_255_);
v___x_264_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_currRecDepth_255_);
lean_ctor_set(v___x_264_, 2, v_ref_256_);
lean_ctor_set_uint16(v___x_264_, sizeof(void*)*3, v___y_243_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*3 + 2, v_suppressElabErrors_257_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*3 + 3, v_checkDeprecated_258_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*3 + 4, v_isRecordingDeps_259_);
v___x_265_ = l_Lean_PrettyPrinter_delab(v_e_218_, v___x_241_, v_a_219_, v_a_220_, v___x_264_, v___y_260_);
lean_dec_ref_known(v___x_264_, 3);
return v___x_265_;
}
v___jp_266_:
{
lean_object* v___x_270_; lean_object* v_env_271_; lean_object* v_nextMacroScope_272_; lean_object* v_ngen_273_; lean_object* v_auxDeclNGen_274_; lean_object* v_traceState_275_; lean_object* v_recordedDeps_276_; lean_object* v_messages_277_; lean_object* v_infoState_278_; lean_object* v_snapshotTasks_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v___x_270_ = lean_st_ref_take(v_a_222_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
v_nextMacroScope_272_ = lean_ctor_get(v___x_270_, 1);
v_ngen_273_ = lean_ctor_get(v___x_270_, 2);
v_auxDeclNGen_274_ = lean_ctor_get(v___x_270_, 3);
v_traceState_275_ = lean_ctor_get(v___x_270_, 4);
v_recordedDeps_276_ = lean_ctor_get(v___x_270_, 6);
v_messages_277_ = lean_ctor_get(v___x_270_, 7);
v_infoState_278_ = lean_ctor_get(v___x_270_, 8);
v_snapshotTasks_279_ = lean_ctor_get(v___x_270_, 9);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_270_, 5);
lean_dec(v_unused_290_);
v___x_281_ = v___x_270_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snapshotTasks_279_);
lean_inc(v_infoState_278_);
lean_inc(v_messages_277_);
lean_inc(v_recordedDeps_276_);
lean_inc(v_traceState_275_);
lean_inc(v_auxDeclNGen_274_);
lean_inc(v_ngen_273_);
lean_inc(v_nextMacroScope_272_);
lean_inc(v_env_271_);
lean_dec(v___x_270_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = l_Lean_Kernel_enableDiag(v_env_271_, v___y_269_);
v___x_284_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 5, v___x_284_);
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_nextMacroScope_272_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_ngen_273_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_auxDeclNGen_274_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_traceState_275_);
lean_ctor_set(v_reuseFailAlloc_288_, 5, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_288_, 6, v_recordedDeps_276_);
lean_ctor_set(v_reuseFailAlloc_288_, 7, v_messages_277_);
lean_ctor_set(v_reuseFailAlloc_288_, 8, v_infoState_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 9, v_snapshotTasks_279_);
v___x_286_ = v_reuseFailAlloc_288_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; 
v___x_287_ = lean_st_ref_put(v_a_222_, v___x_286_);
lean_inc_ref(v_inheritedTraceOptions_240_);
lean_inc(v_cancelTk_x3f_239_);
lean_inc(v_currMacroScope_238_);
lean_inc(v_quotContext_237_);
lean_inc(v_maxHeartbeats_236_);
lean_inc(v_initHeartbeats_235_);
lean_inc(v_openDecls_234_);
lean_inc(v_currNamespace_233_);
lean_inc_ref(v_fileMap_231_);
lean_inc_ref(v_fileName_230_);
v___y_243_ = v___y_267_;
v___y_244_ = v___y_268_;
v_fileName_245_ = v_fileName_230_;
v_fileMap_246_ = v_fileMap_231_;
v_currNamespace_247_ = v_currNamespace_233_;
v_openDecls_248_ = v_openDecls_234_;
v_initHeartbeats_249_ = v_initHeartbeats_235_;
v_maxHeartbeats_250_ = v_maxHeartbeats_236_;
v_quotContext_251_ = v_quotContext_237_;
v_currMacroScope_252_ = v_currMacroScope_238_;
v_cancelTk_x3f_253_ = v_cancelTk_x3f_239_;
v_inheritedTraceOptions_254_ = v_inheritedTraceOptions_240_;
v_currRecDepth_255_ = v_currRecDepth_225_;
v_ref_256_ = v_ref_226_;
v_suppressElabErrors_257_ = v_suppressElabErrors_227_;
v_checkDeprecated_258_ = v_checkDeprecated_228_;
v_isRecordingDeps_259_ = v_isRecordingDeps_229_;
v___y_260_ = v_a_222_;
goto v___jp_242_;
}
}
}
v___jp_291_:
{
uint16_t v___x_293_; lean_object* v___x_294_; lean_object* v_env_295_; uint8_t v___x_296_; uint16_t v___x_297_; uint16_t v___x_298_; uint16_t v___x_299_; uint8_t v___x_300_; 
v___x_293_ = l_Lean_OptionFlags_ofOptions(v___y_292_);
v___x_294_ = lean_st_ref_get(v_a_222_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v___x_296_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_295_);
lean_dec_ref(v_env_295_);
v___x_297_ = 512;
v___x_298_ = lean_uint16_land(v___x_293_, v___x_297_);
v___x_299_ = 0;
v___x_300_ = lean_uint16_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
if (v___x_296_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = 1;
v___y_267_ = v___x_293_;
v___y_268_ = v___y_292_;
v___y_269_ = v___x_301_;
goto v___jp_266_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_240_);
lean_inc(v_cancelTk_x3f_239_);
lean_inc(v_currMacroScope_238_);
lean_inc(v_quotContext_237_);
lean_inc(v_maxHeartbeats_236_);
lean_inc(v_initHeartbeats_235_);
lean_inc(v_openDecls_234_);
lean_inc(v_currNamespace_233_);
lean_inc_ref(v_fileMap_231_);
lean_inc_ref(v_fileName_230_);
v___y_243_ = v___x_293_;
v___y_244_ = v___y_292_;
v_fileName_245_ = v_fileName_230_;
v_fileMap_246_ = v_fileMap_231_;
v_currNamespace_247_ = v_currNamespace_233_;
v_openDecls_248_ = v_openDecls_234_;
v_initHeartbeats_249_ = v_initHeartbeats_235_;
v_maxHeartbeats_250_ = v_maxHeartbeats_236_;
v_quotContext_251_ = v_quotContext_237_;
v_currMacroScope_252_ = v_currMacroScope_238_;
v_cancelTk_x3f_253_ = v_cancelTk_x3f_239_;
v_inheritedTraceOptions_254_ = v_inheritedTraceOptions_240_;
v_currRecDepth_255_ = v_currRecDepth_225_;
v_ref_256_ = v_ref_226_;
v_suppressElabErrors_257_ = v_suppressElabErrors_227_;
v_checkDeprecated_258_ = v_checkDeprecated_228_;
v_isRecordingDeps_259_ = v_isRecordingDeps_229_;
v___y_260_ = v_a_222_;
goto v___jp_242_;
}
}
else
{
if (v___x_296_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_240_);
lean_inc(v_cancelTk_x3f_239_);
lean_inc(v_currMacroScope_238_);
lean_inc(v_quotContext_237_);
lean_inc(v_maxHeartbeats_236_);
lean_inc(v_initHeartbeats_235_);
lean_inc(v_openDecls_234_);
lean_inc(v_currNamespace_233_);
lean_inc_ref(v_fileMap_231_);
lean_inc_ref(v_fileName_230_);
v___y_243_ = v___x_293_;
v___y_244_ = v___y_292_;
v_fileName_245_ = v_fileName_230_;
v_fileMap_246_ = v_fileMap_231_;
v_currNamespace_247_ = v_currNamespace_233_;
v_openDecls_248_ = v_openDecls_234_;
v_initHeartbeats_249_ = v_initHeartbeats_235_;
v_maxHeartbeats_250_ = v_maxHeartbeats_236_;
v_quotContext_251_ = v_quotContext_237_;
v_currMacroScope_252_ = v_currMacroScope_238_;
v_cancelTk_x3f_253_ = v_cancelTk_x3f_239_;
v_inheritedTraceOptions_254_ = v_inheritedTraceOptions_240_;
v_currRecDepth_255_ = v_currRecDepth_225_;
v_ref_256_ = v_ref_226_;
v_suppressElabErrors_257_ = v_suppressElabErrors_227_;
v_checkDeprecated_258_ = v_checkDeprecated_228_;
v_isRecordingDeps_259_ = v_isRecordingDeps_229_;
v___y_260_ = v_a_222_;
goto v___jp_242_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = 0;
v___y_267_ = v___x_293_;
v___y_268_ = v___y_292_;
v___y_269_ = v___x_302_;
goto v___jp_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___boxed(lean_object* v_e_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; lean_object* v_env_320_; uint8_t v___x_321_; lean_object* v_env_322_; lean_object* v___x_323_; lean_object* v_toCold_324_; lean_object* v_mctx_325_; lean_object* v_lctx_326_; lean_object* v_options_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_319_ = lean_st_ref_get(v___y_317_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = 0;
v_env_322_ = l_Lean_Environment_setRecordingDeps(v_env_320_, v___x_321_);
v___x_323_ = lean_st_ref_get(v___y_315_);
v_toCold_324_ = lean_ctor_get(v___y_316_, 0);
v_mctx_325_ = lean_ctor_get(v___x_323_, 0);
lean_inc_ref(v_mctx_325_);
lean_dec(v___x_323_);
v_lctx_326_ = lean_ctor_get(v___y_314_, 2);
v_options_327_ = lean_ctor_get(v_toCold_324_, 2);
lean_inc_ref(v_options_327_);
lean_inc_ref(v_lctx_326_);
v___x_328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_328_, 0, v_env_322_);
lean_ctor_set(v___x_328_, 1, v_mctx_325_);
lean_ctor_set(v___x_328_, 2, v_lctx_326_);
lean_ctor_set(v___x_328_, 3, v_options_327_);
v___x_329_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_msgData_313_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0___boxed(lean_object* v_msgData_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msgData_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object* v_e_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
lean_inc_ref(v_e_341_);
v___x_347_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_363_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = l_Lean_MessageData_ofExpr(v_e_341_);
v___x_350_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_349_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_363_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_355_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1));
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_348_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_a_351_);
v___x_359_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_359_, 0, v___x_356_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
lean_ctor_set(v___x_359_, 2, v___x_357_);
lean_ctor_set(v___x_359_, 3, v___x_357_);
lean_ctor_set(v___x_359_, 4, v___x_358_);
lean_ctor_set(v___x_359_, 5, v___x_357_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_359_);
v___x_361_ = v___x_353_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_e_341_);
v_a_364_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_347_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_347_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___boxed(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_ctor_set(v___x_383_, 3, v___x_382_);
lean_ctor_set(v___x_383_, 4, v___x_381_);
lean_ctor_set(v___x_383_, 5, v___x_381_);
lean_ctor_set(v___x_383_, 6, v___x_381_);
lean_ctor_set(v___x_383_, 7, v___x_381_);
lean_ctor_set(v___x_383_, 8, v___x_381_);
lean_ctor_set(v___x_383_, 9, v___x_381_);
lean_ctor_set(v___x_383_, 10, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(32u);
v___x_385_ = lean_mk_empty_array_with_capacity(v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
size_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = ((size_t)5ULL);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_unsigned_to_nat(32u);
v___x_390_ = lean_mk_empty_array_with_capacity(v___x_389_);
v___x_391_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2);
v___x_392_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
lean_ctor_set(v___x_392_, 2, v___x_388_);
lean_ctor_set(v___x_392_, 3, v___x_388_);
lean_ctor_set_usize(v___x_392_, 4, v___x_387_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_box(1);
v___x_394_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3);
v___x_395_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
v___x_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
lean_ctor_set(v___x_396_, 2, v___x_393_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_toCold_402_; lean_object* v_env_403_; lean_object* v_options_404_; uint8_t v___x_405_; lean_object* v_env_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_toCold_402_ = lean_ctor_get(v___y_398_, 0);
v_env_403_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_401_);
v_options_404_ = lean_ctor_get(v_toCold_402_, 2);
v___x_405_ = 0;
v_env_406_ = l_Lean_Environment_setRecordingDeps(v_env_403_, v___x_405_);
v___x_407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
v___x_408_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4);
lean_inc_ref(v_options_404_);
v___x_409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_409_, 0, v_env_406_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
lean_ctor_set(v___x_409_, 3, v_options_404_);
v___x_410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_msgData_397_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msgData_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(lean_object* v_opts_417_, lean_object* v_opt_418_){
_start:
{
lean_object* v_name_419_; lean_object* v_defValue_420_; lean_object* v_map_421_; lean_object* v___x_422_; 
v_name_419_ = lean_ctor_get(v_opt_418_, 0);
v_defValue_420_ = lean_ctor_get(v_opt_418_, 1);
v_map_421_ = lean_ctor_get(v_opts_417_, 0);
v___x_422_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_421_, v_name_419_);
if (lean_obj_tag(v___x_422_) == 0)
{
uint8_t v___x_423_; 
v___x_423_ = lean_unbox(v_defValue_420_);
return v___x_423_;
}
else
{
lean_object* v_val_424_; 
v_val_424_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v___x_422_, 1);
if (lean_obj_tag(v_val_424_) == 1)
{
uint8_t v_v_425_; 
v_v_425_ = lean_ctor_get_uint8(v_val_424_, 0);
lean_dec_ref_known(v_val_424_, 0);
return v_v_425_;
}
else
{
uint8_t v___x_426_; 
lean_dec(v_val_424_);
v___x_426_ = lean_unbox(v_defValue_420_);
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_427_, lean_object* v_opt_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v_opts_427_, v_opt_428_);
lean_dec_ref(v_opt_428_);
lean_dec_ref(v_opts_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_437_, lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 1)
{
lean_object* v_pre_439_; 
v_pre_439_ = lean_ctor_get(v_x_438_, 0);
switch(lean_obj_tag(v_pre_439_))
{
case 1:
{
lean_object* v_pre_440_; 
v_pre_440_ = lean_ctor_get(v_pre_439_, 0);
switch(lean_obj_tag(v_pre_440_))
{
case 0:
{
lean_object* v_str_441_; lean_object* v_str_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_str_441_ = lean_ctor_get(v_x_438_, 1);
v_str_442_ = lean_ctor_get(v_pre_439_, 1);
v___x_443_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0));
v___x_444_ = lean_string_dec_eq(v_str_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4));
v___x_446_ = lean_string_dec_eq(v_str_442_, v___x_445_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1));
v___x_448_ = lean_string_dec_eq(v_str_441_, v___x_447_);
if (v___x_448_ == 0)
{
return v___x_448_;
}
else
{
return v_suppressElabErrors_437_;
}
}
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2));
v___x_450_ = lean_string_dec_eq(v_str_441_, v___x_449_);
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
return v_suppressElabErrors_437_;
}
}
}
case 1:
{
lean_object* v_pre_451_; 
v_pre_451_ = lean_ctor_get(v_pre_440_, 0);
if (lean_obj_tag(v_pre_451_) == 0)
{
lean_object* v_str_452_; lean_object* v_str_453_; lean_object* v_str_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_str_452_ = lean_ctor_get(v_x_438_, 1);
v_str_453_ = lean_ctor_get(v_pre_439_, 1);
v_str_454_ = lean_ctor_get(v_pre_440_, 1);
v___x_455_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3));
v___x_456_ = lean_string_dec_eq(v_str_454_, v___x_455_);
if (v___x_456_ == 0)
{
return v___x_456_;
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4));
v___x_458_ = lean_string_dec_eq(v_str_453_, v___x_457_);
if (v___x_458_ == 0)
{
return v___x_458_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5));
v___x_460_ = lean_string_dec_eq(v_str_452_, v___x_459_);
if (v___x_460_ == 0)
{
return v___x_460_;
}
else
{
return v_suppressElabErrors_437_;
}
}
}
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
default: 
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
}
case 0:
{
lean_object* v_str_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_str_463_ = lean_ctor_get(v_x_438_, 1);
v___x_464_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1_spec__1___closed__0));
v___x_465_ = lean_string_dec_eq(v_str_463_, v___x_464_);
if (v___x_465_ == 0)
{
return v___x_465_;
}
else
{
return v_suppressElabErrors_437_;
}
}
default: 
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
}
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_suppressElabErrors_boxed_470_; uint8_t v_res_471_; lean_object* v_r_472_; 
v_suppressElabErrors_boxed_470_ = lean_unbox(v_suppressElabErrors_468_);
v_res_471_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_470_, v_x_469_);
lean_dec(v_x_469_);
v_r_472_ = lean_box(v_res_471_);
return v_r_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(lean_object* v_ref_474_, lean_object* v_msgData_475_, uint8_t v_severity_476_, uint8_t v_isSilent_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v_toCold_489_; lean_object* v___y_490_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; uint8_t v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_546_; uint8_t v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; uint8_t v___y_551_; lean_object* v___y_552_; uint8_t v___y_556_; uint8_t v___y_557_; uint8_t v___x_567_; uint8_t v___y_569_; uint8_t v___x_575_; 
v___x_567_ = 2;
v___x_575_ = l_Lean_instBEqMessageSeverity_beq(v_severity_476_, v___x_567_);
if (v___x_575_ == 0)
{
v___y_569_ = v___x_575_;
goto v___jp_568_;
}
else
{
uint8_t v___x_576_; 
lean_inc_ref(v_msgData_475_);
v___x_576_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_475_);
if (v___x_576_ == 0)
{
v___y_569_ = v___x_576_;
goto v___jp_568_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_msgData_475_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
v___jp_481_:
{
lean_object* v_currNamespace_491_; lean_object* v_openDecls_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_env_497_; lean_object* v_nextMacroScope_498_; lean_object* v_ngen_499_; lean_object* v_auxDeclNGen_500_; lean_object* v_traceState_501_; lean_object* v_cache_502_; lean_object* v_recordedDeps_503_; lean_object* v_messages_504_; lean_object* v_infoState_505_; lean_object* v_snapshotTasks_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_517_; 
v_currNamespace_491_ = lean_ctor_get(v_toCold_489_, 4);
v_openDecls_492_ = lean_ctor_get(v_toCold_489_, 5);
lean_inc(v_openDecls_492_);
lean_inc(v_currNamespace_491_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_currNamespace_491_);
lean_ctor_set(v___x_493_, 1, v_openDecls_492_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___y_483_);
lean_inc_ref(v___y_488_);
lean_inc_ref(v___y_487_);
v___x_495_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_495_, 0, v___y_487_);
lean_ctor_set(v___x_495_, 1, v___y_486_);
lean_ctor_set(v___x_495_, 2, v___y_485_);
lean_ctor_set(v___x_495_, 3, v___y_488_);
lean_ctor_set(v___x_495_, 4, v___x_494_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5, v___y_484_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5 + 1, v___y_482_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5 + 2, v_isSilent_477_);
v___x_496_ = lean_st_ref_take(v___y_490_);
v_env_497_ = lean_ctor_get(v___x_496_, 0);
v_nextMacroScope_498_ = lean_ctor_get(v___x_496_, 1);
v_ngen_499_ = lean_ctor_get(v___x_496_, 2);
v_auxDeclNGen_500_ = lean_ctor_get(v___x_496_, 3);
v_traceState_501_ = lean_ctor_get(v___x_496_, 4);
v_cache_502_ = lean_ctor_get(v___x_496_, 5);
v_recordedDeps_503_ = lean_ctor_get(v___x_496_, 6);
v_messages_504_ = lean_ctor_get(v___x_496_, 7);
v_infoState_505_ = lean_ctor_get(v___x_496_, 8);
v_snapshotTasks_506_ = lean_ctor_get(v___x_496_, 9);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_517_ == 0)
{
v___x_508_ = v___x_496_;
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snapshotTasks_506_);
lean_inc(v_infoState_505_);
lean_inc(v_messages_504_);
lean_inc(v_recordedDeps_503_);
lean_inc(v_cache_502_);
lean_inc(v_traceState_501_);
lean_inc(v_auxDeclNGen_500_);
lean_inc(v_ngen_499_);
lean_inc(v_nextMacroScope_498_);
lean_inc(v_env_497_);
lean_dec(v___x_496_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_box(0);
v___x_511_ = l_Lean_MessageLog_add(v___x_495_, v_messages_504_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 7, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_env_497_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_nextMacroScope_498_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_ngen_499_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_auxDeclNGen_500_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_traceState_501_);
lean_ctor_set(v_reuseFailAlloc_516_, 5, v_cache_502_);
lean_ctor_set(v_reuseFailAlloc_516_, 6, v_recordedDeps_503_);
lean_ctor_set(v_reuseFailAlloc_516_, 7, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_516_, 8, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_516_, 9, v_snapshotTasks_506_);
v___x_513_ = v_reuseFailAlloc_516_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_st_ref_put(v___y_490_, v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_510_);
return v___x_515_;
}
}
}
v___jp_518_:
{
lean_object* v_fileName_527_; lean_object* v_fileMap_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_544_; 
v_fileName_527_ = lean_ctor_get(v___y_524_, 0);
v_fileMap_528_ = lean_ctor_get(v___y_524_, 1);
v___x_529_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_475_);
v___x_530_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v___x_529_, v___y_478_, v___y_479_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_544_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_inc_ref_n(v_fileMap_528_, 2);
v___x_535_ = l_Lean_FileMap_toPosition(v_fileMap_528_, v___y_525_);
lean_dec(v___y_525_);
v___x_536_ = l_Lean_FileMap_toPosition(v_fileMap_528_, v___y_526_);
lean_dec(v___y_526_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_522_ == 0)
{
lean_del_object(v___x_533_);
lean_dec_ref(v___y_519_);
v___y_482_ = v___y_521_;
v___y_483_ = v_a_531_;
v___y_484_ = v___y_523_;
v___y_485_ = v___x_537_;
v___y_486_ = v___x_535_;
v___y_487_ = v_fileName_527_;
v___y_488_ = v___x_538_;
v_toCold_489_ = v___y_520_;
v___y_490_ = v___y_479_;
goto v___jp_481_;
}
else
{
uint8_t v___x_539_; 
lean_inc(v_a_531_);
v___x_539_ = l_Lean_MessageData_hasTag(v___y_519_, v_a_531_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_542_; 
lean_dec_ref_known(v___x_537_, 1);
lean_dec_ref(v___x_535_);
lean_dec(v_a_531_);
v___x_540_ = lean_box(0);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_540_);
v___x_542_ = v___x_533_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_del_object(v___x_533_);
v___y_482_ = v___y_521_;
v___y_483_ = v_a_531_;
v___y_484_ = v___y_523_;
v___y_485_ = v___x_537_;
v___y_486_ = v___x_535_;
v___y_487_ = v_fileName_527_;
v___y_488_ = v___x_538_;
v_toCold_489_ = v___y_520_;
v___y_490_ = v___y_479_;
goto v___jp_481_;
}
}
}
}
v___jp_545_:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Syntax_getTailPos_x3f(v___y_549_, v___y_551_);
lean_dec(v___y_549_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_inc(v___y_552_);
v___y_519_ = v___y_546_;
v___y_520_ = v___y_548_;
v___y_521_ = v___y_550_;
v___y_522_ = v___y_547_;
v___y_523_ = v___y_551_;
v___y_524_ = v___y_548_;
v___y_525_ = v___y_552_;
v___y_526_ = v___y_552_;
goto v___jp_518_;
}
else
{
lean_object* v_val_554_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v___x_553_, 1);
v___y_519_ = v___y_546_;
v___y_520_ = v___y_548_;
v___y_521_ = v___y_550_;
v___y_522_ = v___y_547_;
v___y_523_ = v___y_551_;
v___y_524_ = v___y_548_;
v___y_525_ = v___y_552_;
v___y_526_ = v_val_554_;
goto v___jp_518_;
}
}
v___jp_555_:
{
lean_object* v_toCold_558_; lean_object* v_ref_559_; uint8_t v_suppressElabErrors_560_; lean_object* v___x_561_; lean_object* v___f_562_; lean_object* v_ref_563_; lean_object* v___x_564_; 
v_toCold_558_ = lean_ctor_get(v___y_478_, 0);
v_ref_559_ = lean_ctor_get(v___y_478_, 2);
v_suppressElabErrors_560_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 2);
v___x_561_ = lean_box(v_suppressElabErrors_560_);
v___f_562_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_562_, 0, v___x_561_);
v_ref_563_ = l_Lean_replaceRef(v_ref_474_, v_ref_559_);
v___x_564_ = l_Lean_Syntax_getPos_x3f(v_ref_563_, v___y_556_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___y_546_ = v___f_562_;
v___y_547_ = v_suppressElabErrors_560_;
v___y_548_ = v_toCold_558_;
v___y_549_ = v_ref_563_;
v___y_550_ = v___y_557_;
v___y_551_ = v___y_556_;
v___y_552_ = v___x_565_;
goto v___jp_545_;
}
else
{
lean_object* v_val_566_; 
v_val_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_564_, 1);
v___y_546_ = v___f_562_;
v___y_547_ = v_suppressElabErrors_560_;
v___y_548_ = v_toCold_558_;
v___y_549_ = v_ref_563_;
v___y_550_ = v___y_557_;
v___y_551_ = v___y_556_;
v___y_552_ = v_val_566_;
goto v___jp_545_;
}
}
v___jp_568_:
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = 1;
v___x_571_ = l_Lean_instBEqMessageSeverity_beq(v_severity_476_, v___x_570_);
if (v___x_571_ == 0)
{
v___y_556_ = v___y_569_;
v___y_557_ = v_severity_476_;
goto v___jp_555_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_478_);
v___x_573_ = l_Lean_warningAsError;
v___x_574_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v___x_572_, v___x_573_);
lean_dec_ref(v___x_572_);
if (v___x_574_ == 0)
{
v___y_556_ = v___y_569_;
v___y_557_ = v_severity_476_;
goto v___jp_555_;
}
else
{
v___y_556_ = v___y_569_;
v___y_557_ = v___x_567_;
goto v___jp_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___boxed(lean_object* v_ref_579_, lean_object* v_msgData_580_, lean_object* v_severity_581_, lean_object* v_isSilent_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
uint8_t v_severity_boxed_586_; uint8_t v_isSilent_boxed_587_; lean_object* v_res_588_; 
v_severity_boxed_586_ = lean_unbox(v_severity_581_);
v_isSilent_boxed_587_ = lean_unbox(v_isSilent_582_);
v_res_588_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_579_, v_msgData_580_, v_severity_boxed_586_, v_isSilent_boxed_587_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v_ref_579_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object* v_ref_589_, lean_object* v_msgData_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = 0;
v___x_595_ = 0;
v___x_596_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_589_, v_msgData_590_, v___x_594_, v___x_595_, v___y_591_, v___y_592_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object* v_ref_597_, lean_object* v_msgData_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_597_, v_msgData_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v_ref_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* v_ref_603_, lean_object* v_s_604_, lean_object* v_origSpan_x3f_605_, lean_object* v_header_606_, lean_object* v_codeActionPrefix_x3f_607_, uint8_t v_diffGranularity_608_, lean_object* v_footer_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; lean_object* v_hintSuggestion_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; 
v___x_613_ = lean_box(0);
v_hintSuggestion_614_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_hintSuggestion_614_, 0, v_s_604_);
lean_ctor_set(v_hintSuggestion_614_, 1, v_origSpan_x3f_605_);
lean_ctor_set(v_hintSuggestion_614_, 2, v___x_613_);
lean_ctor_set_uint8(v_hintSuggestion_614_, sizeof(void*)*3, v_diffGranularity_608_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_array_push(v___x_616_, v_hintSuggestion_614_);
v___x_618_ = 0;
lean_inc(v_ref_603_);
v___x_619_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v___x_617_, v_ref_603_, v_codeActionPrefix_x3f_607_, v___x_618_, v_a_610_, v_a_611_);
lean_dec_ref(v___x_617_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = l_Lean_stringToMessageData(v_header_606_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_620_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v_footer_609_);
v___x_624_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_603_, v___x_623_, v_a_610_, v_a_611_);
lean_dec(v_ref_603_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_footer_609_);
lean_dec_ref(v_header_606_);
lean_dec(v_ref_603_);
v_a_625_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_619_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_619_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* v_ref_633_, lean_object* v_s_634_, lean_object* v_origSpan_x3f_635_, lean_object* v_header_636_, lean_object* v_codeActionPrefix_x3f_637_, lean_object* v_diffGranularity_638_, lean_object* v_footer_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
uint8_t v_diffGranularity_boxed_643_; lean_object* v_res_644_; 
v_diffGranularity_boxed_643_ = lean_unbox(v_diffGranularity_638_);
v_res_644_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_633_, v_s_634_, v_origSpan_x3f_635_, v_header_636_, v_codeActionPrefix_x3f_637_, v_diffGranularity_boxed_643_, v_footer_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_ref_649_; lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
v_ref_649_ = lean_ctor_get(v___y_646_, 2);
v___x_650_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msg_645_, v___y_646_, v___y_647_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_659_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
lean_inc(v_ref_649_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_ref_649_);
lean_ctor_set(v___x_655_, 1, v_a_651_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 1);
lean_ctor_set(v___x_653_, 0, v___x_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(lean_object* v_ref_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_toCold_670_; lean_object* v_currRecDepth_671_; lean_object* v_ref_672_; uint16_t v_optionFlags_673_; uint8_t v_suppressElabErrors_674_; uint8_t v_checkDeprecated_675_; uint8_t v_isRecordingDeps_676_; lean_object* v_ref_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_toCold_670_ = lean_ctor_get(v___y_667_, 0);
v_currRecDepth_671_ = lean_ctor_get(v___y_667_, 1);
v_ref_672_ = lean_ctor_get(v___y_667_, 2);
v_optionFlags_673_ = lean_ctor_get_uint16(v___y_667_, sizeof(void*)*3);
v_suppressElabErrors_674_ = lean_ctor_get_uint8(v___y_667_, sizeof(void*)*3 + 2);
v_checkDeprecated_675_ = lean_ctor_get_uint8(v___y_667_, sizeof(void*)*3 + 3);
v_isRecordingDeps_676_ = lean_ctor_get_uint8(v___y_667_, sizeof(void*)*3 + 4);
v_ref_677_ = l_Lean_replaceRef(v_ref_665_, v_ref_672_);
lean_inc(v_currRecDepth_671_);
lean_inc_ref(v_toCold_670_);
v___x_678_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_678_, 0, v_toCold_670_);
lean_ctor_set(v___x_678_, 1, v_currRecDepth_671_);
lean_ctor_set(v___x_678_, 2, v_ref_677_);
lean_ctor_set_uint16(v___x_678_, sizeof(void*)*3, v_optionFlags_673_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*3 + 2, v_suppressElabErrors_674_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*3 + 3, v_checkDeprecated_675_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*3 + 4, v_isRecordingDeps_676_);
v___x_679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_666_, v___x_678_, v___y_668_);
lean_dec_ref_known(v___x_678_, 3);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg___boxed(lean_object* v_ref_680_, lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_680_, v_msg_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v_ref_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(lean_object* v_origSpan_x3f_686_, uint8_t v_diffGranularity_687_, size_t v_sz_688_, size_t v_i_689_, lean_object* v_bs_690_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_691_ == 0)
{
lean_dec(v_origSpan_x3f_686_);
return v_bs_690_;
}
else
{
lean_object* v_v_692_; lean_object* v___x_693_; lean_object* v_bs_x27_694_; lean_object* v___x_695_; lean_object* v___x_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v_v_692_ = lean_array_uget(v_bs_690_, v_i_689_);
v___x_693_ = lean_unsigned_to_nat(0u);
v_bs_x27_694_ = lean_array_uset(v_bs_690_, v_i_689_, v___x_693_);
v___x_695_ = lean_box(0);
lean_inc(v_origSpan_x3f_686_);
v___x_696_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_696_, 0, v_v_692_);
lean_ctor_set(v___x_696_, 1, v_origSpan_x3f_686_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*3, v_diffGranularity_687_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_i_689_, v___x_697_);
v___x_699_ = lean_array_uset(v_bs_x27_694_, v_i_689_, v___x_696_);
v_i_689_ = v___x_698_;
v_bs_690_ = v___x_699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object* v_origSpan_x3f_701_, lean_object* v_diffGranularity_702_, lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_bs_705_){
_start:
{
uint8_t v_diffGranularity_boxed_706_; size_t v_sz_boxed_707_; size_t v_i_boxed_708_; lean_object* v_res_709_; 
v_diffGranularity_boxed_706_ = lean_unbox(v_diffGranularity_702_);
v_sz_boxed_707_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_708_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_701_, v_diffGranularity_boxed_706_, v_sz_boxed_707_, v_i_boxed_708_, v_bs_705_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object* v_ref_713_, lean_object* v_suggestions_714_, lean_object* v_origSpan_x3f_715_, lean_object* v_header_716_, lean_object* v_codeActionPrefix_x3f_717_, uint8_t v_diffGranularity_718_, lean_object* v_footer_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_array_get_size(v_suggestions_714_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_nat_dec_eq(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
v___y_724_ = v_a_720_;
v___y_725_ = v_a_721_;
goto v___jp_723_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref(v_footer_719_);
lean_dec(v_codeActionPrefix_x3f_717_);
lean_dec_ref(v_header_716_);
lean_dec(v_origSpan_x3f_715_);
lean_dec_ref(v_suggestions_714_);
v___x_747_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1, &l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1);
v___x_748_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_713_, v___x_747_, v_a_720_, v_a_721_);
lean_dec(v_ref_713_);
return v___x_748_;
}
v___jp_723_:
{
size_t v_sz_726_; size_t v___x_727_; lean_object* v_hintSuggestions_728_; uint8_t v___x_729_; lean_object* v___x_730_; 
v_sz_726_ = lean_array_size(v_suggestions_714_);
v___x_727_ = ((size_t)0ULL);
v_hintSuggestions_728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_715_, v_diffGranularity_718_, v_sz_726_, v___x_727_, v_suggestions_714_);
v___x_729_ = 1;
lean_inc(v_ref_713_);
v___x_730_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_hintSuggestions_728_, v_ref_713_, v_codeActionPrefix_x3f_717_, v___x_729_, v___y_724_, v___y_725_);
lean_dec_ref(v_hintSuggestions_728_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_stringToMessageData(v_header_716_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_a_731_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_footer_719_);
v___x_735_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_713_, v___x_734_, v___y_724_, v___y_725_);
lean_dec(v_ref_713_);
return v___x_735_;
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_footer_719_);
lean_dec_ref(v_header_716_);
lean_dec(v_ref_713_);
v_a_736_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_730_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_730_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(lean_object* v_ref_749_, lean_object* v_suggestions_750_, lean_object* v_origSpan_x3f_751_, lean_object* v_header_752_, lean_object* v_codeActionPrefix_x3f_753_, lean_object* v_diffGranularity_754_, lean_object* v_footer_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_diffGranularity_boxed_759_; lean_object* v_res_760_; 
v_diffGranularity_boxed_759_ = lean_unbox(v_diffGranularity_754_);
v_res_760_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_749_, v_suggestions_750_, v_origSpan_x3f_751_, v_header_752_, v_codeActionPrefix_x3f_753_, v_diffGranularity_boxed_759_, v_footer_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object* v_ref_761_, lean_object* v_suggestions_762_, lean_object* v_origSpan_x3f_763_, lean_object* v_header_764_, lean_object* v_style_x3f_765_, lean_object* v_codeActionPrefix_x3f_766_, uint8_t v_diffGranularity_767_, lean_object* v_footer_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_761_, v_suggestions_762_, v_origSpan_x3f_763_, v_header_764_, v_codeActionPrefix_x3f_766_, v_diffGranularity_767_, v_footer_768_, v_a_769_, v_a_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object* v_ref_773_, lean_object* v_suggestions_774_, lean_object* v_origSpan_x3f_775_, lean_object* v_header_776_, lean_object* v_style_x3f_777_, lean_object* v_codeActionPrefix_x3f_778_, lean_object* v_diffGranularity_779_, lean_object* v_footer_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
uint8_t v_diffGranularity_boxed_784_; lean_object* v_res_785_; 
v_diffGranularity_boxed_784_ = lean_unbox(v_diffGranularity_779_);
v_res_785_ = l_Lean_Meta_Tactic_TryThis_addSuggestions(v_ref_773_, v_suggestions_774_, v_origSpan_x3f_775_, v_header_776_, v_style_x3f_777_, v_codeActionPrefix_x3f_778_, v_diffGranularity_boxed_784_, v_footer_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_style_x3f_777_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object* v_00_u03b1_786_, lean_object* v_ref_787_, lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_787_, v_msg_788_, v___y_789_, v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object* v_00_u03b1_793_, lean_object* v_ref_794_, lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(v_00_u03b1_793_, v_ref_794_, v_msg_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v_ref_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(lean_object* v_00_u03b1_800_, lean_object* v_msg_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___boxed(lean_object* v_00_u03b1_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(v_00_u03b1_806_, v_msg_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(lean_object* v_a_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
v___x_822_ = lean_apply_2(v_a_812_, v___y_813_, v___y_814_);
v___x_823_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_822_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg___boxed(lean_object* v_a_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(lean_object* v_00_u03b1_835_, lean_object* v_a_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___boxed(lean_object* v_00_u03b1_847_, lean_object* v_a_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(v_00_u03b1_847_, v_a_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(lean_object* v_e_859_, lean_object* v___y_860_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = l_Lean_Expr_hasMVar(v_e_859_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_e_859_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; lean_object* v_mctx_865_; lean_object* v___x_866_; lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_869_; lean_object* v_cache_870_; lean_object* v_zetaDeltaFVarIds_871_; lean_object* v_postponed_872_; lean_object* v_diag_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_882_; 
v___x_864_ = lean_st_ref_get(v___y_860_);
v_mctx_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc_ref(v_mctx_865_);
lean_dec(v___x_864_);
v___x_866_ = l_Lean_instantiateMVarsCore(v_mctx_865_, v_e_859_);
v_fst_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_fst_867_);
v_snd_868_ = lean_ctor_get(v___x_866_, 1);
lean_inc(v_snd_868_);
lean_dec_ref(v___x_866_);
v___x_869_ = lean_st_ref_take(v___y_860_);
v_cache_870_ = lean_ctor_get(v___x_869_, 1);
v_zetaDeltaFVarIds_871_ = lean_ctor_get(v___x_869_, 2);
v_postponed_872_ = lean_ctor_get(v___x_869_, 3);
v_diag_873_ = lean_ctor_get(v___x_869_, 4);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v___x_869_, 0);
lean_dec(v_unused_883_);
v___x_875_ = v___x_869_;
v_isShared_876_ = v_isSharedCheck_882_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_diag_873_);
lean_inc(v_postponed_872_);
lean_inc(v_zetaDeltaFVarIds_871_);
lean_inc(v_cache_870_);
lean_dec(v___x_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_882_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_snd_868_);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_snd_868_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_cache_870_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_zetaDeltaFVarIds_871_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_postponed_872_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_diag_873_);
v___x_878_ = v_reuseFailAlloc_881_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_st_ref_put(v___y_860_, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_fst_867_);
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(lean_object* v_e_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_884_, v___y_885_);
lean_dec(v___y_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(lean_object* v_e_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_888_, v___y_894_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(lean_object* v_e_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(lean_object* v_msg_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_ref_916_; lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_ref_916_ = lean_ctor_get(v___y_913_, 2);
v___x_917_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msg_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_inc(v_ref_916_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_ref_916_);
lean_ctor_set(v___x_922_, 1, v_a_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 1);
lean_ctor_set(v___x_920_, 0, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* v_initialState_937_, lean_object* v_tac_938_, lean_object* v_expectedType_x3f_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_941_, v_a_943_, v_a_945_, v_a_947_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; uint8_t v___x_951_; lean_object* v_a_953_; lean_object* v_a_964_; lean_object* v___x_974_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = 0;
v___x_974_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_initialState_937_, v___x_951_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec_ref_known(v___x_974_, 1);
v___x_975_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_975_, 0, v_tac_938_);
v___x_976_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_976_, 0, lean_box(0));
lean_closure_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v___x_976_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_dec_ref_known(v___x_977_, 1);
if (lean_obj_tag(v_expectedType_x3f_939_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v_expectedType_x3f_939_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_expectedType_x3f_939_, 1);
v___x_979_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_941_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_MVarId_getType(v_a_980_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v_a_986_; uint8_t v___x_987_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_982_, v_a_945_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_val_978_, v_a_945_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_expr_eqv(v_a_984_, v_a_986_);
lean_dec(v_a_986_);
lean_dec(v_a_984_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; 
v___x_988_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
v___x_989_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v___x_988_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
v_a_953_ = v_a_990_;
goto v___jp_952_;
}
else
{
lean_object* v___x_991_; 
v___x_991_ = lean_box(0);
v_a_964_ = v___x_991_;
goto v___jp_963_;
}
}
else
{
lean_object* v_a_992_; 
lean_dec(v_val_978_);
v_a_992_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_981_, 1);
v_a_953_ = v_a_992_;
goto v___jp_952_;
}
}
else
{
lean_object* v_a_993_; 
lean_dec(v_val_978_);
v_a_993_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_979_, 1);
v_a_953_ = v_a_993_;
goto v___jp_952_;
}
}
else
{
lean_object* v___x_994_; 
lean_dec(v_expectedType_x3f_939_);
v___x_994_ = lean_box(0);
v_a_964_ = v___x_994_;
goto v___jp_963_;
}
}
else
{
lean_object* v_a_995_; 
lean_dec(v_expectedType_x3f_939_);
v_a_995_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_977_, 1);
v_a_953_ = v_a_995_;
goto v___jp_952_;
}
}
else
{
lean_dec(v_a_950_);
lean_dec(v_expectedType_x3f_939_);
lean_dec(v_tac_938_);
return v___x_974_;
}
v___jp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_950_, v___x_951_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_954_, 0);
lean_dec(v_unused_962_);
v___x_956_ = v___x_954_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_dec(v___x_954_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 1);
lean_ctor_set(v___x_956_, 0, v_a_953_);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_953_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_dec_ref(v_a_953_);
return v___x_954_;
}
}
v___jp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_950_, v___x_951_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v___x_965_, 0);
lean_dec(v_unused_973_);
v___x_967_ = v___x_965_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_dec(v___x_965_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_a_964_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_964_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
return v___x_965_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_expectedType_x3f_939_);
lean_dec(v_tac_938_);
lean_dec_ref(v_initialState_937_);
v_a_996_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_949_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_949_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object* v_initialState_1004_, lean_object* v_tac_1005_, lean_object* v_expectedType_x3f_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1004_, v_tac_1005_, v_expectedType_x3f_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(lean_object* v_00_u03b1_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_1018_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(v_00_u03b1_1029_, v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic(lean_object* v_initialState_1041_, lean_object* v_tac_1042_, lean_object* v_expectedType_x3f_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1045_, v_a_1047_, v_a_1049_, v_a_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1041_, v_tac_1042_, v_expectedType_x3f_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1054_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1055_, 0);
lean_dec(v_unused_1065_);
v___x_1057_ = v___x_1055_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v___x_1055_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1059_ = 1;
v___x_1060_ = lean_box(v___x_1059_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1096_; 
v_a_1066_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1068_ = v___x_1055_;
v_isShared_1069_ = v_isSharedCheck_1096_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1055_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1096_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v___x_1070_; 
v___x_1070_ = l_Lean_Exception_isInterrupt(v_a_1066_);
if (v___x_1070_ == 0)
{
uint8_t v___x_1071_; 
lean_inc(v_a_1066_);
v___x_1071_ = l_Lean_Exception_isRuntime(v_a_1066_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_del_object(v___x_1068_);
lean_dec(v_a_1066_);
v___x_1072_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1054_, v___x_1071_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1072_, 0);
lean_dec(v_unused_1081_);
v___x_1074_ = v___x_1072_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v___x_1072_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_box(v___x_1071_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1072_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1072_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v___x_1091_; 
lean_dec(v_a_1054_);
if (v_isShared_1069_ == 0)
{
v___x_1091_ = v___x_1068_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1066_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_a_1054_);
if (v_isShared_1069_ == 0)
{
v___x_1094_ = v___x_1068_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1066_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_expectedType_x3f_1043_);
lean_dec(v_tac_1042_);
lean_dec_ref(v_initialState_1041_);
v_a_1097_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1053_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1053_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic___boxed(lean_object* v_initialState_1105_, lean_object* v_tac_1106_, lean_object* v_expectedType_x3f_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1105_, v_tac_1106_, v_expectedType_x3f_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* v_tac_1155_, lean_object* v_msg_1156_, lean_object* v_initialState_1157_, lean_object* v_expectedType_x3f_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; 
lean_inc(v_expectedType_x3f_1158_);
lean_inc(v_tac_1155_);
lean_inc_ref(v_initialState_1157_);
v___x_1168_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1157_, v_tac_1155_, v_expectedType_x3f_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1228_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1228_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1228_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_a_1169_);
if (v___x_1173_ == 0)
{
lean_object* v_ref_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_del_object(v___x_1171_);
v_ref_1174_ = lean_ctor_get(v_a_1165_, 2);
v___x_1175_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
v___x_1176_ = l_Lean_SourceInfo_fromRef(v_ref_1174_, v___x_1175_);
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2));
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3));
lean_inc_n(v___x_1176_, 8);
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1176_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5));
v___x_1181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7));
v___x_1182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_1183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11));
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12));
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1176_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node1(v___x_1176_, v___x_1183_, v___x_1185_);
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13));
v___x_1188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1176_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_Syntax_node3(v___x_1176_, v___x_1182_, v___x_1186_, v___x_1188_, v_tac_1155_);
v___x_1190_ = l_Lean_Syntax_node1(v___x_1176_, v___x_1181_, v___x_1189_);
v___x_1191_ = l_Lean_Syntax_node1(v___x_1176_, v___x_1180_, v___x_1190_);
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1176_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node3(v___x_1176_, v___x_1177_, v___x_1179_, v___x_1191_, v___x_1193_);
lean_inc(v___x_1194_);
v___x_1195_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_1157_, v___x_1194_, v_expectedType_x3f_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1214_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1214_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1214_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___x_1200_; 
v___x_1200_ = lean_unbox(v_a_1196_);
lean_dec(v_a_1196_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec(v___x_1194_);
lean_dec_ref(v_msg_1156_);
v___x_1201_ = lean_box(0);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1201_);
v___x_1203_ = v___x_1198_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v_msg_1156_);
v___x_1207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1194_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1210_);
v___x_1212_ = v___x_1198_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v___x_1194_);
lean_dec_ref(v_msg_1156_);
v_a_1215_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1195_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1195_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_dec(v_a_1169_);
lean_dec(v_expectedType_x3f_1158_);
lean_dec_ref(v_initialState_1157_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_tac_1155_);
lean_ctor_set(v___x_1223_, 1, v_msg_1156_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1224_);
v___x_1226_ = v___x_1171_;
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
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_expectedType_x3f_1158_);
lean_dec_ref(v_initialState_1157_);
lean_dec_ref(v_msg_1156_);
lean_dec(v_tac_1155_);
v_a_1229_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1168_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1168_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object* v_tac_1237_, lean_object* v_msg_1238_, lean_object* v_initialState_1239_, lean_object* v_expectedType_x3f_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_tac_1237_, v_msg_1238_, v_initialState_1239_, v_expectedType_x3f_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4));
v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* v_targetKind_1260_, lean_object* v_invalidTactic_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v_targetKind_1260_);
v___x_1264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_indentD(v_invalidTactic_1261_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
v___x_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object* v_e_1288_, uint8_t v_useRefine_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_tac_1301_; lean_object* v___x_1310_; 
lean_inc_ref(v_e_1288_);
v___x_1310_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_1288_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1310_) == 0)
{
if (v_useRefine_1289_ == 0)
{
lean_object* v_a_1311_; lean_object* v_ref_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v_ref_1312_ = lean_ctor_get(v___y_1292_, 2);
v___x_1313_ = l_Lean_SourceInfo_fromRef(v_ref_1312_, v_useRefine_1289_);
v___x_1314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4));
v___x_1315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5));
lean_inc(v___x_1313_);
v___x_1316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1313_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
v___x_1317_ = l_Lean_Syntax_node2(v___x_1313_, v___x_1315_, v___x_1316_, v_a_1311_);
v_tac_1301_ = v___x_1317_;
goto v___jp_1300_;
}
else
{
lean_object* v_a_1318_; lean_object* v_ref_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1310_, 1);
v_ref_1319_ = lean_ctor_get(v___y_1292_, 2);
v___x_1320_ = 0;
v___x_1321_ = l_Lean_SourceInfo_fromRef(v_ref_1319_, v___x_1320_);
v___x_1322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6));
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7));
lean_inc(v___x_1321_);
v___x_1324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
v___x_1325_ = l_Lean_Syntax_node2(v___x_1321_, v___x_1323_, v___x_1324_, v_a_1318_);
v_tac_1301_ = v___x_1325_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_e_1288_);
v_a_1326_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1310_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1310_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
v___jp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___y_1296_);
lean_ctor_set(v___x_1298_, 1, v___y_1297_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
v___jp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = l_Lean_MessageData_ofExpr(v_e_1288_);
v___x_1303_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1302_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (v_useRefine_1289_ == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref(v___x_1303_);
v___x_1305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_a_1304_);
v___y_1296_ = v_tac_1301_;
v___y_1297_ = v___x_1306_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v___x_1303_);
v___x_1308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_a_1307_);
v___y_1296_ = v_tac_1301_;
v___y_1297_ = v___x_1309_;
goto v___jp_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object* v_e_1334_, lean_object* v_useRefine_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_useRefine_boxed_1341_; lean_object* v_res_1342_; 
v_useRefine_boxed_1341_ = lean_unbox(v_useRefine_1335_);
v_res_1342_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_1334_, v_useRefine_boxed_1341_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* v_e_1343_, uint8_t v_useRefine_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_toCold_1350_; lean_object* v_currRecDepth_1351_; lean_object* v_ref_1352_; uint8_t v_suppressElabErrors_1353_; uint8_t v_checkDeprecated_1354_; uint8_t v_isRecordingDeps_1355_; lean_object* v_fileName_1356_; lean_object* v_fileMap_1357_; lean_object* v_options_1358_; lean_object* v_currNamespace_1359_; lean_object* v_openDecls_1360_; lean_object* v_initHeartbeats_1361_; lean_object* v_maxHeartbeats_1362_; lean_object* v_quotContext_1363_; lean_object* v_currMacroScope_1364_; lean_object* v_cancelTk_x3f_1365_; lean_object* v_inheritedTraceOptions_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___y_1370_; uint16_t v___y_1371_; lean_object* v_fileName_1372_; lean_object* v_fileMap_1373_; lean_object* v_currNamespace_1374_; lean_object* v_openDecls_1375_; lean_object* v_initHeartbeats_1376_; lean_object* v_maxHeartbeats_1377_; lean_object* v_quotContext_1378_; lean_object* v_currMacroScope_1379_; lean_object* v_cancelTk_x3f_1380_; lean_object* v_inheritedTraceOptions_1381_; lean_object* v_currRecDepth_1382_; lean_object* v_ref_1383_; uint8_t v_suppressElabErrors_1384_; uint8_t v_checkDeprecated_1385_; uint8_t v_isRecordingDeps_1386_; lean_object* v___y_1387_; uint8_t v___y_1394_; lean_object* v___y_1395_; uint16_t v___y_1396_; lean_object* v___y_1419_; 
v_toCold_1350_ = lean_ctor_get(v_a_1347_, 0);
v_currRecDepth_1351_ = lean_ctor_get(v_a_1347_, 1);
v_ref_1352_ = lean_ctor_get(v_a_1347_, 2);
v_suppressElabErrors_1353_ = lean_ctor_get_uint8(v_a_1347_, sizeof(void*)*3 + 2);
v_checkDeprecated_1354_ = lean_ctor_get_uint8(v_a_1347_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1355_ = lean_ctor_get_uint8(v_a_1347_, sizeof(void*)*3 + 4);
v_fileName_1356_ = lean_ctor_get(v_toCold_1350_, 0);
v_fileMap_1357_ = lean_ctor_get(v_toCold_1350_, 1);
v_options_1358_ = lean_ctor_get(v_toCold_1350_, 2);
v_currNamespace_1359_ = lean_ctor_get(v_toCold_1350_, 4);
v_openDecls_1360_ = lean_ctor_get(v_toCold_1350_, 5);
v_initHeartbeats_1361_ = lean_ctor_get(v_toCold_1350_, 6);
v_maxHeartbeats_1362_ = lean_ctor_get(v_toCold_1350_, 7);
v_quotContext_1363_ = lean_ctor_get(v_toCold_1350_, 8);
v_currMacroScope_1364_ = lean_ctor_get(v_toCold_1350_, 9);
v_cancelTk_x3f_1365_ = lean_ctor_get(v_toCold_1350_, 10);
v_inheritedTraceOptions_1366_ = lean_ctor_get(v_toCold_1350_, 11);
v___x_1367_ = lean_box(v_useRefine_1344_);
v___f_1368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1368_, 0, v_e_1343_);
lean_closure_set(v___f_1368_, 1, v___x_1367_);
if (v_isRecordingDeps_1355_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = l_Lean_pp_mvars;
lean_inc_ref(v_options_1358_);
v___x_1431_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1358_, v___x_1430_, v_isRecordingDeps_1355_);
v___y_1419_ = v___x_1431_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1432_; 
lean_inc_ref(v_options_1358_);
v___x_1432_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1358_);
v___y_1419_ = v___x_1432_;
goto v___jp_1418_;
}
v___jp_1369_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1388_ = l_Lean_maxRecDepth;
v___x_1389_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v___y_1370_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1390_, 0, v_fileName_1372_);
lean_ctor_set(v___x_1390_, 1, v_fileMap_1373_);
lean_ctor_set(v___x_1390_, 2, v___y_1370_);
lean_ctor_set(v___x_1390_, 3, v___x_1389_);
lean_ctor_set(v___x_1390_, 4, v_currNamespace_1374_);
lean_ctor_set(v___x_1390_, 5, v_openDecls_1375_);
lean_ctor_set(v___x_1390_, 6, v_initHeartbeats_1376_);
lean_ctor_set(v___x_1390_, 7, v_maxHeartbeats_1377_);
lean_ctor_set(v___x_1390_, 8, v_quotContext_1378_);
lean_ctor_set(v___x_1390_, 9, v_currMacroScope_1379_);
lean_ctor_set(v___x_1390_, 10, v_cancelTk_x3f_1380_);
lean_ctor_set(v___x_1390_, 11, v_inheritedTraceOptions_1381_);
lean_inc(v_ref_1383_);
lean_inc(v_currRecDepth_1382_);
v___x_1391_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_currRecDepth_1382_);
lean_ctor_set(v___x_1391_, 2, v_ref_1383_);
lean_ctor_set_uint16(v___x_1391_, sizeof(void*)*3, v___y_1371_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*3 + 2, v_suppressElabErrors_1384_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*3 + 3, v_checkDeprecated_1385_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*3 + 4, v_isRecordingDeps_1386_);
v___x_1392_ = l_Lean_Meta_withExposedNames___redArg(v___f_1368_, v_a_1345_, v_a_1346_, v___x_1391_, v___y_1387_);
lean_dec_ref_known(v___x_1391_, 3);
return v___x_1392_;
}
v___jp_1393_:
{
lean_object* v___x_1397_; lean_object* v_env_1398_; lean_object* v_nextMacroScope_1399_; lean_object* v_ngen_1400_; lean_object* v_auxDeclNGen_1401_; lean_object* v_traceState_1402_; lean_object* v_recordedDeps_1403_; lean_object* v_messages_1404_; lean_object* v_infoState_1405_; lean_object* v_snapshotTasks_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1416_; 
v___x_1397_ = lean_st_ref_take(v_a_1348_);
v_env_1398_ = lean_ctor_get(v___x_1397_, 0);
v_nextMacroScope_1399_ = lean_ctor_get(v___x_1397_, 1);
v_ngen_1400_ = lean_ctor_get(v___x_1397_, 2);
v_auxDeclNGen_1401_ = lean_ctor_get(v___x_1397_, 3);
v_traceState_1402_ = lean_ctor_get(v___x_1397_, 4);
v_recordedDeps_1403_ = lean_ctor_get(v___x_1397_, 6);
v_messages_1404_ = lean_ctor_get(v___x_1397_, 7);
v_infoState_1405_ = lean_ctor_get(v___x_1397_, 8);
v_snapshotTasks_1406_ = lean_ctor_get(v___x_1397_, 9);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v___x_1397_, 5);
lean_dec(v_unused_1417_);
v___x_1408_ = v___x_1397_;
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_snapshotTasks_1406_);
lean_inc(v_infoState_1405_);
lean_inc(v_messages_1404_);
lean_inc(v_recordedDeps_1403_);
lean_inc(v_traceState_1402_);
lean_inc(v_auxDeclNGen_1401_);
lean_inc(v_ngen_1400_);
lean_inc(v_nextMacroScope_1399_);
lean_inc(v_env_1398_);
lean_dec(v___x_1397_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1410_ = l_Lean_Kernel_enableDiag(v_env_1398_, v___y_1394_);
v___x_1411_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 5, v___x_1411_);
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_nextMacroScope_1399_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_ngen_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_auxDeclNGen_1401_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_traceState_1402_);
lean_ctor_set(v_reuseFailAlloc_1415_, 5, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1415_, 6, v_recordedDeps_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 7, v_messages_1404_);
lean_ctor_set(v_reuseFailAlloc_1415_, 8, v_infoState_1405_);
lean_ctor_set(v_reuseFailAlloc_1415_, 9, v_snapshotTasks_1406_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_st_ref_put(v_a_1348_, v___x_1413_);
lean_inc_ref(v_inheritedTraceOptions_1366_);
lean_inc(v_cancelTk_x3f_1365_);
lean_inc(v_currMacroScope_1364_);
lean_inc(v_quotContext_1363_);
lean_inc(v_maxHeartbeats_1362_);
lean_inc(v_initHeartbeats_1361_);
lean_inc(v_openDecls_1360_);
lean_inc(v_currNamespace_1359_);
lean_inc_ref(v_fileMap_1357_);
lean_inc_ref(v_fileName_1356_);
v___y_1370_ = v___y_1395_;
v___y_1371_ = v___y_1396_;
v_fileName_1372_ = v_fileName_1356_;
v_fileMap_1373_ = v_fileMap_1357_;
v_currNamespace_1374_ = v_currNamespace_1359_;
v_openDecls_1375_ = v_openDecls_1360_;
v_initHeartbeats_1376_ = v_initHeartbeats_1361_;
v_maxHeartbeats_1377_ = v_maxHeartbeats_1362_;
v_quotContext_1378_ = v_quotContext_1363_;
v_currMacroScope_1379_ = v_currMacroScope_1364_;
v_cancelTk_x3f_1380_ = v_cancelTk_x3f_1365_;
v_inheritedTraceOptions_1381_ = v_inheritedTraceOptions_1366_;
v_currRecDepth_1382_ = v_currRecDepth_1351_;
v_ref_1383_ = v_ref_1352_;
v_suppressElabErrors_1384_ = v_suppressElabErrors_1353_;
v_checkDeprecated_1385_ = v_checkDeprecated_1354_;
v_isRecordingDeps_1386_ = v_isRecordingDeps_1355_;
v___y_1387_ = v_a_1348_;
goto v___jp_1369_;
}
}
}
v___jp_1418_:
{
uint16_t v___x_1420_; lean_object* v___x_1421_; lean_object* v_env_1422_; uint8_t v___x_1423_; uint16_t v___x_1424_; uint16_t v___x_1425_; uint16_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1420_ = l_Lean_OptionFlags_ofOptions(v___y_1419_);
v___x_1421_ = lean_st_ref_get(v_a_1348_);
v_env_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc_ref(v_env_1422_);
lean_dec(v___x_1421_);
v___x_1423_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1422_);
lean_dec_ref(v_env_1422_);
v___x_1424_ = 512;
v___x_1425_ = lean_uint16_land(v___x_1420_, v___x_1424_);
v___x_1426_ = 0;
v___x_1427_ = lean_uint16_dec_eq(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
if (v___x_1423_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = 1;
v___y_1394_ = v___x_1428_;
v___y_1395_ = v___y_1419_;
v___y_1396_ = v___x_1420_;
goto v___jp_1393_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1366_);
lean_inc(v_cancelTk_x3f_1365_);
lean_inc(v_currMacroScope_1364_);
lean_inc(v_quotContext_1363_);
lean_inc(v_maxHeartbeats_1362_);
lean_inc(v_initHeartbeats_1361_);
lean_inc(v_openDecls_1360_);
lean_inc(v_currNamespace_1359_);
lean_inc_ref(v_fileMap_1357_);
lean_inc_ref(v_fileName_1356_);
v___y_1370_ = v___y_1419_;
v___y_1371_ = v___x_1420_;
v_fileName_1372_ = v_fileName_1356_;
v_fileMap_1373_ = v_fileMap_1357_;
v_currNamespace_1374_ = v_currNamespace_1359_;
v_openDecls_1375_ = v_openDecls_1360_;
v_initHeartbeats_1376_ = v_initHeartbeats_1361_;
v_maxHeartbeats_1377_ = v_maxHeartbeats_1362_;
v_quotContext_1378_ = v_quotContext_1363_;
v_currMacroScope_1379_ = v_currMacroScope_1364_;
v_cancelTk_x3f_1380_ = v_cancelTk_x3f_1365_;
v_inheritedTraceOptions_1381_ = v_inheritedTraceOptions_1366_;
v_currRecDepth_1382_ = v_currRecDepth_1351_;
v_ref_1383_ = v_ref_1352_;
v_suppressElabErrors_1384_ = v_suppressElabErrors_1353_;
v_checkDeprecated_1385_ = v_checkDeprecated_1354_;
v_isRecordingDeps_1386_ = v_isRecordingDeps_1355_;
v___y_1387_ = v_a_1348_;
goto v___jp_1369_;
}
}
else
{
if (v___x_1423_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1366_);
lean_inc(v_cancelTk_x3f_1365_);
lean_inc(v_currMacroScope_1364_);
lean_inc(v_quotContext_1363_);
lean_inc(v_maxHeartbeats_1362_);
lean_inc(v_initHeartbeats_1361_);
lean_inc(v_openDecls_1360_);
lean_inc(v_currNamespace_1359_);
lean_inc_ref(v_fileMap_1357_);
lean_inc_ref(v_fileName_1356_);
v___y_1370_ = v___y_1419_;
v___y_1371_ = v___x_1420_;
v_fileName_1372_ = v_fileName_1356_;
v_fileMap_1373_ = v_fileMap_1357_;
v_currNamespace_1374_ = v_currNamespace_1359_;
v_openDecls_1375_ = v_openDecls_1360_;
v_initHeartbeats_1376_ = v_initHeartbeats_1361_;
v_maxHeartbeats_1377_ = v_maxHeartbeats_1362_;
v_quotContext_1378_ = v_quotContext_1363_;
v_currMacroScope_1379_ = v_currMacroScope_1364_;
v_cancelTk_x3f_1380_ = v_cancelTk_x3f_1365_;
v_inheritedTraceOptions_1381_ = v_inheritedTraceOptions_1366_;
v_currRecDepth_1382_ = v_currRecDepth_1351_;
v_ref_1383_ = v_ref_1352_;
v_suppressElabErrors_1384_ = v_suppressElabErrors_1353_;
v_checkDeprecated_1385_ = v_checkDeprecated_1354_;
v_isRecordingDeps_1386_ = v_isRecordingDeps_1355_;
v___y_1387_ = v_a_1348_;
goto v___jp_1369_;
}
else
{
uint8_t v___x_1429_; 
v___x_1429_ = 0;
v___y_1394_ = v___x_1429_;
v___y_1395_ = v___y_1419_;
v___y_1396_ = v___x_1420_;
goto v___jp_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* v_e_1433_, lean_object* v_useRefine_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
uint8_t v_useRefine_boxed_1440_; lean_object* v_res_1441_; 
v_useRefine_boxed_1440_ = lean_unbox(v_useRefine_1434_);
v_res_1441_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1433_, v_useRefine_boxed_1440_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(lean_object* v_as_1445_, size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_b_1448_);
return v___x_1455_;
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_array_uget_borrowed(v_as_1445_, v_i_1447_);
lean_inc(v_a_1456_);
v___x_1457_ = l_Lean_MVarId_getType(v_a_1456_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_1458_, v___y_1450_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___boxed), 6, 1);
lean_closure_set(v___x_1461_, 0, v_a_1460_);
v___x_1462_ = l_Lean_Meta_withExposedNames___redArg(v___x_1461_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1));
v___x_1465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
lean_ctor_set(v___x_1465_, 1, v_a_1463_);
v___x_1466_ = l_Std_Format_defWidth;
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = l_Std_Format_pretty(v___x_1465_, v___x_1466_, v___x_1467_, v___x_1467_);
v___x_1469_ = lean_string_append(v_b_1448_, v___x_1468_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = lean_usize_add(v_i_1447_, v___x_1470_);
v_i_1447_ = v___x_1471_;
v_b_1448_ = v___x_1469_;
goto _start;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_b_1448_);
v_a_1473_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1462_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1462_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_b_1448_);
v_a_1481_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1459_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1459_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_b_1448_);
v_a_1489_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1457_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1457_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(lean_object* v_as_1497_, lean_object* v_sz_1498_, lean_object* v_i_1499_, lean_object* v_b_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
size_t v_sz_boxed_1506_; size_t v_i_boxed_1507_; lean_object* v_res_1508_; 
v_sz_boxed_1506_ = lean_unbox_usize(v_sz_1498_);
lean_dec(v_sz_1498_);
v_i_boxed_1507_ = lean_unbox_usize(v_i_1499_);
lean_dec(v_i_1499_);
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1497_, v_sz_boxed_1506_, v_i_boxed_1507_, v_b_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec_ref(v_as_1497_);
return v_res_1508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t v_addSubgoalsMsg_1520_, lean_object* v_checkState_x3f_1521_, lean_object* v_e_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_postInfo_x3f_1546_; lean_object* v___y_1555_; lean_object* v___y_1556_; uint8_t v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; uint8_t v___y_1563_; uint16_t v___y_1649_; lean_object* v___y_1650_; lean_object* v_fileName_1651_; lean_object* v_fileMap_1652_; lean_object* v_currNamespace_1653_; lean_object* v_openDecls_1654_; lean_object* v_initHeartbeats_1655_; lean_object* v_maxHeartbeats_1656_; lean_object* v_quotContext_1657_; lean_object* v_currMacroScope_1658_; lean_object* v_cancelTk_x3f_1659_; lean_object* v_inheritedTraceOptions_1660_; lean_object* v_currRecDepth_1661_; lean_object* v_ref_1662_; uint8_t v_suppressElabErrors_1663_; uint8_t v_checkDeprecated_1664_; uint8_t v_isRecordingDeps_1665_; lean_object* v___y_1666_; lean_object* v_toCold_1686_; lean_object* v_currRecDepth_1687_; lean_object* v_ref_1688_; uint8_t v_suppressElabErrors_1689_; uint8_t v_checkDeprecated_1690_; uint8_t v_isRecordingDeps_1691_; lean_object* v_fileName_1692_; lean_object* v_fileMap_1693_; lean_object* v_options_1694_; lean_object* v_currNamespace_1695_; lean_object* v_openDecls_1696_; lean_object* v_initHeartbeats_1697_; lean_object* v_maxHeartbeats_1698_; lean_object* v_quotContext_1699_; lean_object* v_currMacroScope_1700_; lean_object* v_cancelTk_x3f_1701_; lean_object* v_inheritedTraceOptions_1702_; uint8_t v___y_1704_; uint16_t v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1729_; 
v_toCold_1686_ = lean_ctor_get(v_a_1529_, 0);
v_currRecDepth_1687_ = lean_ctor_get(v_a_1529_, 1);
v_ref_1688_ = lean_ctor_get(v_a_1529_, 2);
v_suppressElabErrors_1689_ = lean_ctor_get_uint8(v_a_1529_, sizeof(void*)*3 + 2);
v_checkDeprecated_1690_ = lean_ctor_get_uint8(v_a_1529_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1691_ = lean_ctor_get_uint8(v_a_1529_, sizeof(void*)*3 + 4);
v_fileName_1692_ = lean_ctor_get(v_toCold_1686_, 0);
v_fileMap_1693_ = lean_ctor_get(v_toCold_1686_, 1);
v_options_1694_ = lean_ctor_get(v_toCold_1686_, 2);
v_currNamespace_1695_ = lean_ctor_get(v_toCold_1686_, 4);
v_openDecls_1696_ = lean_ctor_get(v_toCold_1686_, 5);
v_initHeartbeats_1697_ = lean_ctor_get(v_toCold_1686_, 6);
v_maxHeartbeats_1698_ = lean_ctor_get(v_toCold_1686_, 7);
v_quotContext_1699_ = lean_ctor_get(v_toCold_1686_, 8);
v_currMacroScope_1700_ = lean_ctor_get(v_toCold_1686_, 9);
v_cancelTk_x3f_1701_ = lean_ctor_get(v_toCold_1686_, 10);
v_inheritedTraceOptions_1702_ = lean_ctor_get(v_toCold_1686_, 11);
if (v_isRecordingDeps_1691_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = l_Lean_pp_mvars;
lean_inc_ref(v_options_1694_);
v___x_1741_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1694_, v___x_1740_, v_isRecordingDeps_1691_);
v___y_1729_ = v___x_1741_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1742_; 
lean_inc_ref(v_options_1694_);
v___x_1742_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1694_);
v___y_1729_ = v___x_1742_;
goto v___jp_1728_;
}
v___jp_1532_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_inc_ref(v___y_1535_);
v___x_1536_ = l_Lean_stringToMessageData(v___y_1535_);
lean_inc_ref(v___y_1534_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___y_1534_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_1539_, v___y_1533_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
v___jp_1543_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___y_1545_);
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___y_1544_);
v___x_1551_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
lean_ctor_set(v___x_1551_, 2, v_postInfo_x3f_1546_);
lean_ctor_set(v___x_1551_, 3, v___x_1549_);
lean_ctor_set(v___x_1551_, 4, v___x_1550_);
lean_ctor_set(v___x_1551_, 5, v___x_1549_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
v___jp_1554_:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_box(0);
v___y_1544_ = v___y_1555_;
v___y_1545_ = v___y_1556_;
v_postInfo_x3f_1546_ = v___x_1557_;
goto v___jp_1543_;
}
v___jp_1558_:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1522_, v___y_1563_, v_a_1527_, v_a_1528_, v___y_1561_, v___y_1560_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1639_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1639_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1639_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
if (lean_obj_tag(v_checkState_x3f_1521_) == 1)
{
lean_object* v_fst_1569_; lean_object* v_snd_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1567_);
v_fst_1569_ = lean_ctor_get(v_a_1565_, 0);
v_snd_1570_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1572_ = v_a_1565_;
v_isShared_1573_ = v_isSharedCheck_1622_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snd_1570_);
lean_inc(v_fst_1569_);
lean_dec(v_a_1565_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1622_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_val_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_val_1574_ = lean_ctor_get(v_checkState_x3f_1521_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v_checkState_x3f_1521_, 1);
v___x_1575_ = lean_box(0);
lean_inc(v_snd_1570_);
v___x_1576_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_1569_, v_snd_1570_, v_val_1574_, v___x_1575_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v___y_1561_, v___y_1560_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
if (lean_obj_tag(v_a_1577_) == 1)
{
lean_object* v_val_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1572_);
lean_dec(v_snd_1570_);
v_val_1578_ = lean_ctor_get(v_a_1577_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_a_1577_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1580_ = v_a_1577_;
v_isShared_1581_ = v_isSharedCheck_1604_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_val_1578_);
lean_dec(v_a_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1604_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
if (v_addSubgoalsMsg_1520_ == 0)
{
lean_object* v_fst_1582_; lean_object* v_snd_1583_; 
lean_del_object(v___x_1580_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
v_fst_1582_ = lean_ctor_get(v_val_1578_, 0);
lean_inc(v_fst_1582_);
v_snd_1583_ = lean_ctor_get(v_val_1578_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_val_1578_);
v___y_1555_ = v_snd_1583_;
v___y_1556_ = v_fst_1582_;
goto v___jp_1554_;
}
else
{
if (v___y_1559_ == 0)
{
lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_fst_1584_ = lean_ctor_get(v_val_1578_, 0);
lean_inc(v_fst_1584_);
v_snd_1585_ = lean_ctor_get(v_val_1578_, 1);
lean_inc(v_snd_1585_);
lean_dec(v_val_1578_);
v___x_1586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4));
v_sz_1587_ = lean_array_size(v___y_1562_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v___y_1562_, v_sz_1587_, v___x_1588_, v___x_1586_, v_a_1527_, v_a_1528_, v___y_1561_, v___y_1560_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v___y_1562_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_a_1590_);
v___x_1592_ = v___x_1580_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
v___y_1544_ = v_snd_1585_;
v___y_1545_ = v_fst_1584_;
v_postInfo_x3f_1546_ = v___x_1592_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_del_object(v___x_1580_);
v_a_1594_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1589_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1589_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_fst_1602_; lean_object* v_snd_1603_; 
lean_del_object(v___x_1580_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
v_fst_1602_ = lean_ctor_get(v_val_1578_, 0);
lean_inc(v_fst_1602_);
v_snd_1603_ = lean_ctor_get(v_val_1578_, 1);
lean_inc(v_snd_1603_);
lean_dec(v_val_1578_);
v___y_1555_ = v_snd_1603_;
v___y_1556_ = v_fst_1602_;
goto v___jp_1554_;
}
}
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_dec(v_a_1577_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
v___x_1605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 7);
lean_ctor_set(v___x_1572_, 0, v___x_1605_);
v___x_1607_ = v___x_1572_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_snd_1570_);
v___x_1607_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6);
if (v___y_1563_ == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_1533_ = v___x_1609_;
v___y_1534_ = v___x_1610_;
v___y_1535_ = v___x_1611_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7));
v___y_1533_ = v___x_1609_;
v___y_1534_ = v___x_1610_;
v___y_1535_ = v___x_1612_;
goto v___jp_1532_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_del_object(v___x_1572_);
lean_dec(v_snd_1570_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
v_a_1614_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1576_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1576_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v_fst_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v_checkState_x3f_1521_);
v_fst_1623_ = lean_ctor_get(v_a_1565_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_a_1565_, 1);
lean_dec(v_unused_1638_);
v___x_1625_ = v_a_1565_;
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_fst_1623_);
lean_dec(v_a_1565_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v_fst_1623_);
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_fst_1623_);
v___x_1629_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
lean_ctor_set(v___x_1631_, 2, v___x_1630_);
lean_ctor_set(v___x_1631_, 3, v___x_1630_);
lean_ctor_set(v___x_1631_, 4, v___x_1630_);
lean_ctor_set(v___x_1631_, 5, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1632_);
v___x_1634_ = v___x_1567_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v_checkState_x3f_1521_);
v_a_1640_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1564_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1564_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
v___jp_1648_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1667_ = l_Lean_maxRecDepth;
v___x_1668_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v___y_1650_, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1669_, 0, v_fileName_1651_);
lean_ctor_set(v___x_1669_, 1, v_fileMap_1652_);
lean_ctor_set(v___x_1669_, 2, v___y_1650_);
lean_ctor_set(v___x_1669_, 3, v___x_1668_);
lean_ctor_set(v___x_1669_, 4, v_currNamespace_1653_);
lean_ctor_set(v___x_1669_, 5, v_openDecls_1654_);
lean_ctor_set(v___x_1669_, 6, v_initHeartbeats_1655_);
lean_ctor_set(v___x_1669_, 7, v_maxHeartbeats_1656_);
lean_ctor_set(v___x_1669_, 8, v_quotContext_1657_);
lean_ctor_set(v___x_1669_, 9, v_currMacroScope_1658_);
lean_ctor_set(v___x_1669_, 10, v_cancelTk_x3f_1659_);
lean_ctor_set(v___x_1669_, 11, v_inheritedTraceOptions_1660_);
lean_inc(v_ref_1662_);
lean_inc(v_currRecDepth_1661_);
v___x_1670_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_currRecDepth_1661_);
lean_ctor_set(v___x_1670_, 2, v_ref_1662_);
lean_ctor_set_uint16(v___x_1670_, sizeof(void*)*3, v___y_1649_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 2, v_suppressElabErrors_1663_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 3, v_checkDeprecated_1664_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 4, v_isRecordingDeps_1665_);
lean_inc_ref(v_e_1522_);
v___x_1671_ = l_Lean_Meta_getMVars(v_e_1522_, v_a_1527_, v_a_1528_, v___x_1670_, v___y_1666_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = lean_array_get_size(v_a_1672_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_nat_dec_eq(v___x_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; 
v___x_1676_ = 1;
v___y_1559_ = v___x_1675_;
v___y_1560_ = v___y_1666_;
v___y_1561_ = v___x_1670_;
v___y_1562_ = v_a_1672_;
v___y_1563_ = v___x_1676_;
goto v___jp_1558_;
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = 0;
v___y_1559_ = v___x_1675_;
v___y_1560_ = v___y_1666_;
v___y_1561_ = v___x_1670_;
v___y_1562_ = v_a_1672_;
v___y_1563_ = v___x_1677_;
goto v___jp_1558_;
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref_known(v___x_1670_, 3);
lean_dec_ref(v_e_1522_);
lean_dec(v_checkState_x3f_1521_);
v_a_1678_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1671_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1671_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
v___jp_1703_:
{
lean_object* v___x_1707_; lean_object* v_env_1708_; lean_object* v_nextMacroScope_1709_; lean_object* v_ngen_1710_; lean_object* v_auxDeclNGen_1711_; lean_object* v_traceState_1712_; lean_object* v_recordedDeps_1713_; lean_object* v_messages_1714_; lean_object* v_infoState_1715_; lean_object* v_snapshotTasks_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1726_; 
v___x_1707_ = lean_st_ref_take(v_a_1530_);
v_env_1708_ = lean_ctor_get(v___x_1707_, 0);
v_nextMacroScope_1709_ = lean_ctor_get(v___x_1707_, 1);
v_ngen_1710_ = lean_ctor_get(v___x_1707_, 2);
v_auxDeclNGen_1711_ = lean_ctor_get(v___x_1707_, 3);
v_traceState_1712_ = lean_ctor_get(v___x_1707_, 4);
v_recordedDeps_1713_ = lean_ctor_get(v___x_1707_, 6);
v_messages_1714_ = lean_ctor_get(v___x_1707_, 7);
v_infoState_1715_ = lean_ctor_get(v___x_1707_, 8);
v_snapshotTasks_1716_ = lean_ctor_get(v___x_1707_, 9);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1707_, 5);
lean_dec(v_unused_1727_);
v___x_1718_ = v___x_1707_;
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_snapshotTasks_1716_);
lean_inc(v_infoState_1715_);
lean_inc(v_messages_1714_);
lean_inc(v_recordedDeps_1713_);
lean_inc(v_traceState_1712_);
lean_inc(v_auxDeclNGen_1711_);
lean_inc(v_ngen_1710_);
lean_inc(v_nextMacroScope_1709_);
lean_inc(v_env_1708_);
lean_dec(v___x_1707_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = l_Lean_Kernel_enableDiag(v_env_1708_, v___y_1704_);
v___x_1721_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 5, v___x_1721_);
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1723_ = v___x_1718_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1709_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1710_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1711_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_traceState_1712_);
lean_ctor_set(v_reuseFailAlloc_1725_, 5, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_recordedDeps_1713_);
lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_messages_1714_);
lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_infoState_1715_);
lean_ctor_set(v_reuseFailAlloc_1725_, 9, v_snapshotTasks_1716_);
v___x_1723_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_st_ref_put(v_a_1530_, v___x_1723_);
lean_inc_ref(v_inheritedTraceOptions_1702_);
lean_inc(v_cancelTk_x3f_1701_);
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_1699_);
lean_inc(v_maxHeartbeats_1698_);
lean_inc(v_initHeartbeats_1697_);
lean_inc(v_openDecls_1696_);
lean_inc(v_currNamespace_1695_);
lean_inc_ref(v_fileMap_1693_);
lean_inc_ref(v_fileName_1692_);
v___y_1649_ = v___y_1705_;
v___y_1650_ = v___y_1706_;
v_fileName_1651_ = v_fileName_1692_;
v_fileMap_1652_ = v_fileMap_1693_;
v_currNamespace_1653_ = v_currNamespace_1695_;
v_openDecls_1654_ = v_openDecls_1696_;
v_initHeartbeats_1655_ = v_initHeartbeats_1697_;
v_maxHeartbeats_1656_ = v_maxHeartbeats_1698_;
v_quotContext_1657_ = v_quotContext_1699_;
v_currMacroScope_1658_ = v_currMacroScope_1700_;
v_cancelTk_x3f_1659_ = v_cancelTk_x3f_1701_;
v_inheritedTraceOptions_1660_ = v_inheritedTraceOptions_1702_;
v_currRecDepth_1661_ = v_currRecDepth_1687_;
v_ref_1662_ = v_ref_1688_;
v_suppressElabErrors_1663_ = v_suppressElabErrors_1689_;
v_checkDeprecated_1664_ = v_checkDeprecated_1690_;
v_isRecordingDeps_1665_ = v_isRecordingDeps_1691_;
v___y_1666_ = v_a_1530_;
goto v___jp_1648_;
}
}
}
v___jp_1728_:
{
uint16_t v___x_1730_; lean_object* v___x_1731_; lean_object* v_env_1732_; uint8_t v___x_1733_; uint16_t v___x_1734_; uint16_t v___x_1735_; uint16_t v___x_1736_; uint8_t v___x_1737_; 
v___x_1730_ = l_Lean_OptionFlags_ofOptions(v___y_1729_);
v___x_1731_ = lean_st_ref_get(v_a_1530_);
v_env_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc_ref(v_env_1732_);
lean_dec(v___x_1731_);
v___x_1733_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1732_);
lean_dec_ref(v_env_1732_);
v___x_1734_ = 512;
v___x_1735_ = lean_uint16_land(v___x_1730_, v___x_1734_);
v___x_1736_ = 0;
v___x_1737_ = lean_uint16_dec_eq(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
if (v___x_1733_ == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = 1;
v___y_1704_ = v___x_1738_;
v___y_1705_ = v___x_1730_;
v___y_1706_ = v___y_1729_;
goto v___jp_1703_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1702_);
lean_inc(v_cancelTk_x3f_1701_);
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_1699_);
lean_inc(v_maxHeartbeats_1698_);
lean_inc(v_initHeartbeats_1697_);
lean_inc(v_openDecls_1696_);
lean_inc(v_currNamespace_1695_);
lean_inc_ref(v_fileMap_1693_);
lean_inc_ref(v_fileName_1692_);
v___y_1649_ = v___x_1730_;
v___y_1650_ = v___y_1729_;
v_fileName_1651_ = v_fileName_1692_;
v_fileMap_1652_ = v_fileMap_1693_;
v_currNamespace_1653_ = v_currNamespace_1695_;
v_openDecls_1654_ = v_openDecls_1696_;
v_initHeartbeats_1655_ = v_initHeartbeats_1697_;
v_maxHeartbeats_1656_ = v_maxHeartbeats_1698_;
v_quotContext_1657_ = v_quotContext_1699_;
v_currMacroScope_1658_ = v_currMacroScope_1700_;
v_cancelTk_x3f_1659_ = v_cancelTk_x3f_1701_;
v_inheritedTraceOptions_1660_ = v_inheritedTraceOptions_1702_;
v_currRecDepth_1661_ = v_currRecDepth_1687_;
v_ref_1662_ = v_ref_1688_;
v_suppressElabErrors_1663_ = v_suppressElabErrors_1689_;
v_checkDeprecated_1664_ = v_checkDeprecated_1690_;
v_isRecordingDeps_1665_ = v_isRecordingDeps_1691_;
v___y_1666_ = v_a_1530_;
goto v___jp_1648_;
}
}
else
{
if (v___x_1733_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_1702_);
lean_inc(v_cancelTk_x3f_1701_);
lean_inc(v_currMacroScope_1700_);
lean_inc(v_quotContext_1699_);
lean_inc(v_maxHeartbeats_1698_);
lean_inc(v_initHeartbeats_1697_);
lean_inc(v_openDecls_1696_);
lean_inc(v_currNamespace_1695_);
lean_inc_ref(v_fileMap_1693_);
lean_inc_ref(v_fileName_1692_);
v___y_1649_ = v___x_1730_;
v___y_1650_ = v___y_1729_;
v_fileName_1651_ = v_fileName_1692_;
v_fileMap_1652_ = v_fileMap_1693_;
v_currNamespace_1653_ = v_currNamespace_1695_;
v_openDecls_1654_ = v_openDecls_1696_;
v_initHeartbeats_1655_ = v_initHeartbeats_1697_;
v_maxHeartbeats_1656_ = v_maxHeartbeats_1698_;
v_quotContext_1657_ = v_quotContext_1699_;
v_currMacroScope_1658_ = v_currMacroScope_1700_;
v_cancelTk_x3f_1659_ = v_cancelTk_x3f_1701_;
v_inheritedTraceOptions_1660_ = v_inheritedTraceOptions_1702_;
v_currRecDepth_1661_ = v_currRecDepth_1687_;
v_ref_1662_ = v_ref_1688_;
v_suppressElabErrors_1663_ = v_suppressElabErrors_1689_;
v_checkDeprecated_1664_ = v_checkDeprecated_1690_;
v_isRecordingDeps_1665_ = v_isRecordingDeps_1691_;
v___y_1666_ = v_a_1530_;
goto v___jp_1648_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
v___y_1704_ = v___x_1739_;
v___y_1705_ = v___x_1730_;
v___y_1706_ = v___y_1729_;
goto v___jp_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* v_addSubgoalsMsg_1743_, lean_object* v_checkState_x3f_1744_, lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1755_; lean_object* v_res_1756_; 
v_addSubgoalsMsg_boxed_1755_ = lean_unbox(v_addSubgoalsMsg_1743_);
v_res_1756_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_boxed_1755_, v_checkState_x3f_1744_, v_e_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object* v_as_1757_, size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_b_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1757_, v_sz_1758_, v_i_1759_, v_b_1760_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object* v_as_1771_, lean_object* v_sz_1772_, lean_object* v_i_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
size_t v_sz_boxed_1784_; size_t v_i_boxed_1785_; lean_object* v_res_1786_; 
v_sz_boxed_1784_ = lean_unbox_usize(v_sz_1772_);
lean_dec(v_sz_1772_);
v_i_boxed_1785_ = lean_unbox_usize(v_i_1773_);
lean_dec(v_i_1773_);
v_res_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_1771_, v_sz_boxed_1784_, v_i_boxed_1785_, v_b_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_as_1771_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1787_, lean_object* v_msgData_1788_, uint8_t v_severity_1789_, uint8_t v_isSilent_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v_toCold_1804_; lean_object* v___y_1805_; lean_object* v___y_1834_; lean_object* v___y_1835_; uint8_t v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; uint8_t v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1871_; uint8_t v___y_1872_; uint8_t v___x_1882_; uint8_t v___y_1884_; uint8_t v___x_1890_; 
v___x_1882_ = 2;
v___x_1890_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1789_, v___x_1882_);
if (v___x_1890_ == 0)
{
v___y_1884_ = v___x_1890_;
goto v___jp_1883_;
}
else
{
uint8_t v___x_1891_; 
lean_inc_ref(v_msgData_1788_);
v___x_1891_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1788_);
if (v___x_1891_ == 0)
{
v___y_1884_ = v___x_1891_;
goto v___jp_1883_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec_ref(v_msgData_1788_);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
v___jp_1796_:
{
lean_object* v_currNamespace_1806_; lean_object* v_openDecls_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v_env_1812_; lean_object* v_nextMacroScope_1813_; lean_object* v_ngen_1814_; lean_object* v_auxDeclNGen_1815_; lean_object* v_traceState_1816_; lean_object* v_cache_1817_; lean_object* v_recordedDeps_1818_; lean_object* v_messages_1819_; lean_object* v_infoState_1820_; lean_object* v_snapshotTasks_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1832_; 
v_currNamespace_1806_ = lean_ctor_get(v_toCold_1804_, 4);
v_openDecls_1807_ = lean_ctor_get(v_toCold_1804_, 5);
lean_inc(v_openDecls_1807_);
lean_inc(v_currNamespace_1806_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_currNamespace_1806_);
lean_ctor_set(v___x_1808_, 1, v_openDecls_1807_);
v___x_1809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___y_1797_);
lean_inc_ref(v___y_1802_);
lean_inc_ref(v___y_1799_);
v___x_1810_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1810_, 0, v___y_1799_);
lean_ctor_set(v___x_1810_, 1, v___y_1798_);
lean_ctor_set(v___x_1810_, 2, v___y_1801_);
lean_ctor_set(v___x_1810_, 3, v___y_1802_);
lean_ctor_set(v___x_1810_, 4, v___x_1809_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*5, v___y_1803_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*5 + 1, v___y_1800_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*5 + 2, v_isSilent_1790_);
v___x_1811_ = lean_st_ref_take(v___y_1805_);
v_env_1812_ = lean_ctor_get(v___x_1811_, 0);
v_nextMacroScope_1813_ = lean_ctor_get(v___x_1811_, 1);
v_ngen_1814_ = lean_ctor_get(v___x_1811_, 2);
v_auxDeclNGen_1815_ = lean_ctor_get(v___x_1811_, 3);
v_traceState_1816_ = lean_ctor_get(v___x_1811_, 4);
v_cache_1817_ = lean_ctor_get(v___x_1811_, 5);
v_recordedDeps_1818_ = lean_ctor_get(v___x_1811_, 6);
v_messages_1819_ = lean_ctor_get(v___x_1811_, 7);
v_infoState_1820_ = lean_ctor_get(v___x_1811_, 8);
v_snapshotTasks_1821_ = lean_ctor_get(v___x_1811_, 9);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1823_ = v___x_1811_;
v_isShared_1824_ = v_isSharedCheck_1832_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_snapshotTasks_1821_);
lean_inc(v_infoState_1820_);
lean_inc(v_messages_1819_);
lean_inc(v_recordedDeps_1818_);
lean_inc(v_cache_1817_);
lean_inc(v_traceState_1816_);
lean_inc(v_auxDeclNGen_1815_);
lean_inc(v_ngen_1814_);
lean_inc(v_nextMacroScope_1813_);
lean_inc(v_env_1812_);
lean_dec(v___x_1811_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1832_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = l_Lean_MessageLog_add(v___x_1810_, v_messages_1819_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 7, v___x_1826_);
v___x_1828_ = v___x_1823_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_env_1812_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_nextMacroScope_1813_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_ngen_1814_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_auxDeclNGen_1815_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v_traceState_1816_);
lean_ctor_set(v_reuseFailAlloc_1831_, 5, v_cache_1817_);
lean_ctor_set(v_reuseFailAlloc_1831_, 6, v_recordedDeps_1818_);
lean_ctor_set(v_reuseFailAlloc_1831_, 7, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1831_, 8, v_infoState_1820_);
lean_ctor_set(v_reuseFailAlloc_1831_, 9, v_snapshotTasks_1821_);
v___x_1828_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_st_ref_put(v___y_1805_, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1825_);
return v___x_1830_;
}
}
}
v___jp_1833_:
{
lean_object* v_fileName_1842_; lean_object* v_fileMap_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1859_; 
v_fileName_1842_ = lean_ctor_get(v___y_1838_, 0);
v_fileMap_1843_ = lean_ctor_get(v___y_1838_, 1);
v___x_1844_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1788_);
v___x_1845_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1844_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_inc_ref_n(v_fileMap_1843_, 2);
v___x_1850_ = l_Lean_FileMap_toPosition(v_fileMap_1843_, v___y_1840_);
lean_dec(v___y_1840_);
v___x_1851_ = l_Lean_FileMap_toPosition(v_fileMap_1843_, v___y_1841_);
lean_dec(v___y_1841_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
v___x_1853_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_1836_ == 0)
{
lean_del_object(v___x_1848_);
lean_dec_ref(v___y_1835_);
v___y_1797_ = v_a_1846_;
v___y_1798_ = v___x_1850_;
v___y_1799_ = v_fileName_1842_;
v___y_1800_ = v___y_1837_;
v___y_1801_ = v___x_1852_;
v___y_1802_ = v___x_1853_;
v___y_1803_ = v___y_1839_;
v_toCold_1804_ = v___y_1834_;
v___y_1805_ = v___y_1794_;
goto v___jp_1796_;
}
else
{
uint8_t v___x_1854_; 
lean_inc(v_a_1846_);
v___x_1854_ = l_Lean_MessageData_hasTag(v___y_1835_, v_a_1846_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec_ref_known(v___x_1852_, 1);
lean_dec_ref(v___x_1850_);
lean_dec(v_a_1846_);
v___x_1855_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1855_);
v___x_1857_ = v___x_1848_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
lean_del_object(v___x_1848_);
v___y_1797_ = v_a_1846_;
v___y_1798_ = v___x_1850_;
v___y_1799_ = v_fileName_1842_;
v___y_1800_ = v___y_1837_;
v___y_1801_ = v___x_1852_;
v___y_1802_ = v___x_1853_;
v___y_1803_ = v___y_1839_;
v_toCold_1804_ = v___y_1834_;
v___y_1805_ = v___y_1794_;
goto v___jp_1796_;
}
}
}
}
v___jp_1860_:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Syntax_getTailPos_x3f(v___y_1866_, v___y_1865_);
lean_dec(v___y_1866_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_inc(v___y_1867_);
v___y_1834_ = v___y_1862_;
v___y_1835_ = v___y_1863_;
v___y_1836_ = v___y_1861_;
v___y_1837_ = v___y_1864_;
v___y_1838_ = v___y_1862_;
v___y_1839_ = v___y_1865_;
v___y_1840_ = v___y_1867_;
v___y_1841_ = v___y_1867_;
goto v___jp_1833_;
}
else
{
lean_object* v_val_1869_; 
v_val_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___y_1834_ = v___y_1862_;
v___y_1835_ = v___y_1863_;
v___y_1836_ = v___y_1861_;
v___y_1837_ = v___y_1864_;
v___y_1838_ = v___y_1862_;
v___y_1839_ = v___y_1865_;
v___y_1840_ = v___y_1867_;
v___y_1841_ = v_val_1869_;
goto v___jp_1833_;
}
}
v___jp_1870_:
{
lean_object* v_toCold_1873_; lean_object* v_ref_1874_; uint8_t v_suppressElabErrors_1875_; lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v_ref_1878_; lean_object* v___x_1879_; 
v_toCold_1873_ = lean_ctor_get(v___y_1793_, 0);
v_ref_1874_ = lean_ctor_get(v___y_1793_, 2);
v_suppressElabErrors_1875_ = lean_ctor_get_uint8(v___y_1793_, sizeof(void*)*3 + 2);
v___x_1876_ = lean_box(v_suppressElabErrors_1875_);
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1877_, 0, v___x_1876_);
v_ref_1878_ = l_Lean_replaceRef(v_ref_1787_, v_ref_1874_);
v___x_1879_ = l_Lean_Syntax_getPos_x3f(v_ref_1878_, v___y_1871_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___y_1861_ = v_suppressElabErrors_1875_;
v___y_1862_ = v_toCold_1873_;
v___y_1863_ = v___f_1877_;
v___y_1864_ = v___y_1872_;
v___y_1865_ = v___y_1871_;
v___y_1866_ = v_ref_1878_;
v___y_1867_ = v___x_1880_;
goto v___jp_1860_;
}
else
{
lean_object* v_val_1881_; 
v_val_1881_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v___x_1879_, 1);
v___y_1861_ = v_suppressElabErrors_1875_;
v___y_1862_ = v_toCold_1873_;
v___y_1863_ = v___f_1877_;
v___y_1864_ = v___y_1872_;
v___y_1865_ = v___y_1871_;
v___y_1866_ = v_ref_1878_;
v___y_1867_ = v_val_1881_;
goto v___jp_1860_;
}
}
v___jp_1883_:
{
uint8_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = 1;
v___x_1886_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1789_, v___x_1885_);
if (v___x_1886_ == 0)
{
v___y_1871_ = v___y_1884_;
v___y_1872_ = v_severity_1789_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1887_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1793_);
v___x_1888_ = l_Lean_warningAsError;
v___x_1889_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__2(v___x_1887_, v___x_1888_);
lean_dec_ref(v___x_1887_);
if (v___x_1889_ == 0)
{
v___y_1871_ = v___y_1884_;
v___y_1872_ = v_severity_1789_;
goto v___jp_1870_;
}
else
{
v___y_1871_ = v___y_1884_;
v___y_1872_ = v___x_1882_;
goto v___jp_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1894_, lean_object* v_msgData_1895_, lean_object* v_severity_1896_, lean_object* v_isSilent_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
uint8_t v_severity_boxed_1903_; uint8_t v_isSilent_boxed_1904_; lean_object* v_res_1905_; 
v_severity_boxed_1903_ = lean_unbox(v_severity_1896_);
v_isSilent_boxed_1904_ = lean_unbox(v_isSilent_1897_);
v_res_1905_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1894_, v_msgData_1895_, v_severity_boxed_1903_, v_isSilent_boxed_1904_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v_ref_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(lean_object* v_msgData_1906_, uint8_t v_severity_1907_, uint8_t v_isSilent_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_ref_1918_; lean_object* v___x_1919_; 
v_ref_1918_ = lean_ctor_get(v___y_1915_, 2);
v___x_1919_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1918_, v_msgData_1906_, v_severity_1907_, v_isSilent_1908_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(lean_object* v_msgData_1920_, lean_object* v_severity_1921_, lean_object* v_isSilent_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
uint8_t v_severity_boxed_1932_; uint8_t v_isSilent_boxed_1933_; lean_object* v_res_1934_; 
v_severity_boxed_1932_ = lean_unbox(v_severity_1921_);
v_isSilent_boxed_1933_ = lean_unbox(v_isSilent_1922_);
v_res_1934_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1920_, v_severity_boxed_1932_, v_isSilent_boxed_1933_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object* v_msgData_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v___x_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = 0;
v___x_1946_ = 0;
v___x_1947_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1935_, v___x_1945_, v___x_1946_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object* v_msgData_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_msgData_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* v_ref_1960_, lean_object* v_e_1961_, lean_object* v_origSpan_x3f_1962_, uint8_t v_addSubgoalsMsg_1963_, lean_object* v_codeActionPrefix_x3f_1964_, lean_object* v_checkState_x3f_1965_, uint8_t v_tacticErrorAsInfo_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_1963_, v_checkState_x3f_1965_, v_e_1961_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v_val_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_val_1978_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v_a_1977_, 1);
v___x_1979_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_1980_ = 4;
v___x_1981_ = l_Lean_MessageData_nil;
v___x_1982_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_1960_, v_val_1978_, v_origSpan_x3f_1962_, v___x_1979_, v_codeActionPrefix_x3f_1964_, v___x_1980_, v___x_1981_, v_a_1973_, v_a_1974_);
return v___x_1982_;
}
else
{
lean_dec(v_codeActionPrefix_x3f_1964_);
lean_dec(v_origSpan_x3f_1962_);
lean_dec(v_ref_1960_);
if (v_tacticErrorAsInfo_1966_ == 0)
{
lean_object* v_val_1983_; lean_object* v___x_1984_; 
v_val_1983_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v_a_1977_, 1);
v___x_1984_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_1983_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_1984_;
}
else
{
lean_object* v_val_1985_; lean_object* v___x_1986_; 
v_val_1985_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v_a_1977_, 1);
v___x_1986_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_val_1985_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_codeActionPrefix_x3f_1964_);
lean_dec(v_origSpan_x3f_1962_);
lean_dec(v_ref_1960_);
v_a_1987_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1976_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1976_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* v_ref_1995_, lean_object* v_e_1996_, lean_object* v_origSpan_x3f_1997_, lean_object* v_addSubgoalsMsg_1998_, lean_object* v_codeActionPrefix_x3f_1999_, lean_object* v_checkState_x3f_2000_, lean_object* v_tacticErrorAsInfo_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2011_; uint8_t v_tacticErrorAsInfo_boxed_2012_; lean_object* v_res_2013_; 
v_addSubgoalsMsg_boxed_2011_ = lean_unbox(v_addSubgoalsMsg_1998_);
v_tacticErrorAsInfo_boxed_2012_ = lean_unbox(v_tacticErrorAsInfo_2001_);
v_res_2013_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_ref_1995_, v_e_1996_, v_origSpan_x3f_1997_, v_addSubgoalsMsg_boxed_2011_, v_codeActionPrefix_x3f_1999_, v_checkState_x3f_2000_, v_tacticErrorAsInfo_boxed_2012_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(lean_object* v_ref_2014_, lean_object* v_msgData_2015_, uint8_t v_severity_2016_, uint8_t v_isSilent_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_2014_, v_msgData_2015_, v_severity_2016_, v_isSilent_2017_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2028_, lean_object* v_msgData_2029_, lean_object* v_severity_2030_, lean_object* v_isSilent_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_severity_boxed_2041_; uint8_t v_isSilent_boxed_2042_; lean_object* v_res_2043_; 
v_severity_boxed_2041_ = lean_unbox(v_severity_2030_);
v_isSilent_boxed_2042_ = lean_unbox(v_isSilent_2031_);
v_res_2043_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_2028_, v_msgData_2029_, v_severity_boxed_2041_, v_isSilent_boxed_2042_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v_ref_2028_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(uint8_t v_tacticErrorAsInfo_2044_, lean_object* v_as_2045_, size_t v_sz_2046_, size_t v_i_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_a_2055_; uint8_t v___x_2059_; 
v___x_2059_ = lean_usize_dec_lt(v_i_2047_, v_sz_2046_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_b_2048_);
return v___x_2060_;
}
else
{
lean_object* v_fst_2061_; lean_object* v_snd_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2087_; 
v_fst_2061_ = lean_ctor_get(v_b_2048_, 0);
v_snd_2062_ = lean_ctor_get(v_b_2048_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_b_2048_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2064_ = v_b_2048_;
v_isShared_2065_ = v_isSharedCheck_2087_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_snd_2062_);
lean_inc(v_fst_2061_);
lean_dec(v_b_2048_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2087_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_array_uget_borrowed(v_as_2045_, v_i_2047_);
if (lean_obj_tag(v_a_2066_) == 0)
{
lean_object* v_val_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v_val_2067_ = lean_ctor_get(v_a_2066_, 0);
lean_inc(v_val_2067_);
v___x_2068_ = lean_array_push(v_fst_2061_, v_val_2067_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2068_);
v___x_2070_ = v___x_2064_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_snd_2062_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
v_a_2055_ = v___x_2070_;
goto v___jp_2054_;
}
}
else
{
lean_object* v_val_2072_; 
v_val_2072_ = lean_ctor_get(v_a_2066_, 0);
if (v_tacticErrorAsInfo_2044_ == 0)
{
lean_object* v___x_2078_; 
lean_inc(v_val_2072_);
v___x_2078_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_2072_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_dec_ref_known(v___x_2078_, 1);
goto v___jp_2073_;
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_del_object(v___x_2064_);
lean_dec(v_snd_2062_);
lean_dec(v_fst_2061_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
goto v___jp_2073_;
}
v___jp_2073_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_inc(v_val_2072_);
v___x_2074_ = lean_array_push(v_snd_2062_, v_val_2072_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___x_2074_);
v___x_2076_ = v___x_2064_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_fst_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
v_a_2055_ = v___x_2076_;
goto v___jp_2054_;
}
}
}
}
}
v___jp_2054_:
{
size_t v___x_2056_; size_t v___x_2057_; 
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2047_, v___x_2056_);
v_i_2047_ = v___x_2057_;
v_b_2048_ = v_a_2055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(lean_object* v_tacticErrorAsInfo_2088_, lean_object* v_as_2089_, lean_object* v_sz_2090_, lean_object* v_i_2091_, lean_object* v_b_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2098_; size_t v_sz_boxed_2099_; size_t v_i_boxed_2100_; lean_object* v_res_2101_; 
v_tacticErrorAsInfo_boxed_2098_ = lean_unbox(v_tacticErrorAsInfo_2088_);
v_sz_boxed_2099_ = lean_unbox_usize(v_sz_2090_);
lean_dec(v_sz_2090_);
v_i_boxed_2100_ = lean_unbox_usize(v_i_2091_);
lean_dec(v_i_2091_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_boxed_2098_, v_as_2089_, v_sz_boxed_2099_, v_i_boxed_2100_, v_b_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec_ref(v_as_2089_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t v_addSubgoalsMsg_2102_, lean_object* v_checkState_x3f_2103_, size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_bs_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_usize_dec_lt(v_i_2105_, v_sz_2104_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v_checkState_x3f_2103_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_bs_2106_);
return v___x_2117_;
}
else
{
lean_object* v_v_2118_; lean_object* v___x_2119_; lean_object* v_bs_x27_2120_; lean_object* v___x_2121_; 
v_v_2118_ = lean_array_uget(v_bs_2106_, v_i_2105_);
v___x_2119_ = lean_unsigned_to_nat(0u);
v_bs_x27_2120_ = lean_array_uset(v_bs_2106_, v_i_2105_, v___x_2119_);
lean_inc(v_checkState_x3f_2103_);
v___x_2121_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_2102_, v_checkState_x3f_2103_, v_v_2118_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = ((size_t)1ULL);
v___x_2124_ = lean_usize_add(v_i_2105_, v___x_2123_);
v___x_2125_ = lean_array_uset(v_bs_x27_2120_, v_i_2105_, v_a_2122_);
v_i_2105_ = v___x_2124_;
v_bs_2106_ = v___x_2125_;
goto _start;
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_bs_x27_2120_);
lean_dec(v_checkState_x3f_2103_);
v_a_2127_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2121_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2121_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object* v_addSubgoalsMsg_2135_, lean_object* v_checkState_x3f_2136_, lean_object* v_sz_2137_, lean_object* v_i_2138_, lean_object* v_bs_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2149_; size_t v_sz_boxed_2150_; size_t v_i_boxed_2151_; lean_object* v_res_2152_; 
v_addSubgoalsMsg_boxed_2149_ = lean_unbox(v_addSubgoalsMsg_2135_);
v_sz_boxed_2150_ = lean_unbox_usize(v_sz_2137_);
lean_dec(v_sz_2137_);
v_i_boxed_2151_ = lean_unbox_usize(v_i_2138_);
lean_dec(v_i_2138_);
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_boxed_2149_, v_checkState_x3f_2136_, v_sz_boxed_2150_, v_i_boxed_2151_, v_bs_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(lean_object* v_as_2153_, size_t v_sz_2154_, size_t v_i_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_lt(v_i_2155_, v_sz_2154_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_b_2156_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; lean_object* v_a_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_box(0);
v_a_2169_ = lean_array_uget_borrowed(v_as_2153_, v_i_2155_);
lean_inc(v_a_2169_);
v___x_2170_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_a_2169_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2170_) == 0)
{
size_t v___x_2171_; size_t v___x_2172_; 
lean_dec_ref_known(v___x_2170_, 1);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2155_, v___x_2171_);
v_i_2155_ = v___x_2172_;
v_b_2156_ = v___x_2168_;
goto _start;
}
else
{
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(lean_object* v_as_2174_, lean_object* v_sz_2175_, lean_object* v_i_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
size_t v_sz_boxed_2187_; size_t v_i_boxed_2188_; lean_object* v_res_2189_; 
v_sz_boxed_2187_ = lean_unbox_usize(v_sz_2175_);
lean_dec(v_sz_2175_);
v_i_boxed_2188_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_2174_, v_sz_boxed_2187_, v_i_boxed_2188_, v_b_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec_ref(v_as_2174_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* v_ref_2195_, lean_object* v_es_2196_, lean_object* v_origSpan_x3f_2197_, uint8_t v_addSubgoalsMsg_2198_, lean_object* v_codeActionPrefix_x3f_2199_, lean_object* v_checkState_x3f_2200_, uint8_t v_tacticErrorAsInfo_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
size_t v_sz_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_sz_2211_ = lean_array_size(v_es_2196_);
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_2198_, v_checkState_x3f_2200_, v_sz_2211_, v___x_2212_, v_es_2196_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; size_t v_sz_2216_; lean_object* v___x_2217_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1));
v_sz_2216_ = lean_array_size(v_a_2214_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2201_, v_a_2214_, v_sz_2216_, v___x_2212_, v___x_2215_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2214_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v_fst_2219_; lean_object* v_snd_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v_fst_2219_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_fst_2219_);
v_snd_2220_ = lean_ctor_get(v_a_2218_, 1);
lean_inc(v_snd_2220_);
lean_dec(v_a_2218_);
v___x_2221_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2));
v___x_2222_ = 4;
v___x_2223_ = l_Lean_MessageData_nil;
v___x_2224_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2195_, v_fst_2219_, v_origSpan_x3f_2197_, v___x_2221_, v_codeActionPrefix_x3f_2199_, v___x_2222_, v___x_2223_, v_a_2208_, v_a_2209_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2225_; size_t v_sz_2226_; lean_object* v___x_2227_; 
lean_dec_ref_known(v___x_2224_, 1);
v___x_2225_ = lean_box(0);
v_sz_2226_ = lean_array_size(v_snd_2220_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_snd_2220_, v_sz_2226_, v___x_2212_, v___x_2225_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_snd_2220_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v___x_2227_, 0);
lean_dec(v_unused_2235_);
v___x_2229_ = v___x_2227_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v___x_2227_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2225_);
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2225_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
return v___x_2227_;
}
}
else
{
lean_dec(v_snd_2220_);
return v___x_2224_;
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_codeActionPrefix_x3f_2199_);
lean_dec(v_origSpan_x3f_2197_);
lean_dec(v_ref_2195_);
v_a_2236_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2217_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2217_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_codeActionPrefix_x3f_2199_);
lean_dec(v_origSpan_x3f_2197_);
lean_dec(v_ref_2195_);
v_a_2244_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2213_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2213_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* v_ref_2252_, lean_object* v_es_2253_, lean_object* v_origSpan_x3f_2254_, lean_object* v_addSubgoalsMsg_2255_, lean_object* v_codeActionPrefix_x3f_2256_, lean_object* v_checkState_x3f_2257_, lean_object* v_tacticErrorAsInfo_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2268_; uint8_t v_tacticErrorAsInfo_boxed_2269_; lean_object* v_res_2270_; 
v_addSubgoalsMsg_boxed_2268_ = lean_unbox(v_addSubgoalsMsg_2255_);
v_tacticErrorAsInfo_boxed_2269_ = lean_unbox(v_tacticErrorAsInfo_2258_);
v_res_2270_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(v_ref_2252_, v_es_2253_, v_origSpan_x3f_2254_, v_addSubgoalsMsg_boxed_2268_, v_codeActionPrefix_x3f_2256_, v_checkState_x3f_2257_, v_tacticErrorAsInfo_boxed_2269_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t v_tacticErrorAsInfo_2271_, lean_object* v_as_2272_, size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_b_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2271_, v_as_2272_, v_sz_2273_, v_i_2274_, v_b_2275_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object* v_tacticErrorAsInfo_2286_, lean_object* v_as_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2300_; size_t v_sz_boxed_2301_; size_t v_i_boxed_2302_; lean_object* v_res_2303_; 
v_tacticErrorAsInfo_boxed_2300_ = lean_unbox(v_tacticErrorAsInfo_2286_);
v_sz_boxed_2301_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2302_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_boxed_2300_, v_as_2287_, v_sz_boxed_2301_, v_i_boxed_2302_, v_b_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_as_2287_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* v_ref_2304_, lean_object* v_e_2305_, lean_object* v_origSpan_x3f_2306_, lean_object* v_header_2307_, lean_object* v_codeActionPrefix_x3f_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_2305_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = 4;
v___x_2317_ = l_Lean_MessageData_nil;
v___x_2318_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2304_, v_a_2315_, v_origSpan_x3f_2306_, v_header_2307_, v_codeActionPrefix_x3f_2308_, v___x_2316_, v___x_2317_, v_a_2311_, v_a_2312_);
return v___x_2318_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_codeActionPrefix_x3f_2308_);
lean_dec_ref(v_header_2307_);
lean_dec(v_origSpan_x3f_2306_);
lean_dec(v_ref_2304_);
v_a_2319_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2314_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2314_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object* v_ref_2327_, lean_object* v_e_2328_, lean_object* v_origSpan_x3f_2329_, lean_object* v_header_2330_, lean_object* v_codeActionPrefix_x3f_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_ref_2327_, v_e_2328_, v_origSpan_x3f_2329_, v_header_2330_, v_codeActionPrefix_x3f_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_bs_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_usize_dec_lt(v_i_2339_, v_sz_2338_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v_bs_2340_);
return v___x_2347_;
}
else
{
lean_object* v_v_2348_; lean_object* v___x_2349_; lean_object* v_bs_x27_2350_; lean_object* v___x_2351_; 
v_v_2348_ = lean_array_uget(v_bs_2340_, v_i_2339_);
v___x_2349_ = lean_unsigned_to_nat(0u);
v_bs_x27_2350_ = lean_array_uset(v_bs_2340_, v_i_2339_, v___x_2349_);
v___x_2351_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_v_2348_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = ((size_t)1ULL);
v___x_2354_ = lean_usize_add(v_i_2339_, v___x_2353_);
v___x_2355_ = lean_array_uset(v_bs_x27_2350_, v_i_2339_, v_a_2352_);
v_i_2339_ = v___x_2354_;
v_bs_2340_ = v___x_2355_;
goto _start;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_bs_x27_2350_);
v_a_2357_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2351_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2351_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object* v_sz_2365_, lean_object* v_i_2366_, lean_object* v_bs_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
size_t v_sz_boxed_2373_; size_t v_i_boxed_2374_; lean_object* v_res_2375_; 
v_sz_boxed_2373_ = lean_unbox_usize(v_sz_2365_);
lean_dec(v_sz_2365_);
v_i_boxed_2374_ = lean_unbox_usize(v_i_2366_);
lean_dec(v_i_2366_);
v_res_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_boxed_2373_, v_i_boxed_2374_, v_bs_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* v_ref_2376_, lean_object* v_es_2377_, lean_object* v_origSpan_x3f_2378_, lean_object* v_header_2379_, lean_object* v_codeActionPrefix_x3f_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
size_t v_sz_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v_sz_2386_ = lean_array_size(v_es_2377_);
v___x_2387_ = ((size_t)0ULL);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_2386_, v___x_2387_, v_es_2377_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = 4;
v___x_2391_ = l_Lean_MessageData_nil;
v___x_2392_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2376_, v_a_2389_, v_origSpan_x3f_2378_, v_header_2379_, v_codeActionPrefix_x3f_2380_, v___x_2390_, v___x_2391_, v_a_2383_, v_a_2384_);
return v___x_2392_;
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_codeActionPrefix_x3f_2380_);
lean_dec_ref(v_header_2379_);
lean_dec(v_origSpan_x3f_2378_);
lean_dec(v_ref_2376_);
v_a_2393_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2388_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2388_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object* v_ref_2401_, lean_object* v_es_2402_, lean_object* v_origSpan_x3f_2403_, lean_object* v_header_2404_, lean_object* v_codeActionPrefix_x3f_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(v_ref_2401_, v_es_2402_, v_origSpan_x3f_2403_, v_header_2404_, v_codeActionPrefix_x3f_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2411_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Array_mkArray0___redArg();
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14));
v___x_2448_ = l_Lean_stringToMessageData(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16));
v___x_2451_ = l_Lean_stringToMessageData(v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21));
v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_2476_ = l_String_toRawSubstring_x27(v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80));
v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82));
v___x_2618_ = l_Lean_stringToMessageData(v___x_2617_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84));
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object* v_e_2622_, lean_object* v_t_x3f_2623_, uint8_t v_a_2624_, lean_object* v_h_x3f_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v___x_2644_; 
lean_inc_ref(v_e_2622_);
v___x_2644_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_2622_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___y_2647_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
if (lean_obj_tag(v_t_x3f_2623_) == 1)
{
lean_object* v_val_2675_; lean_object* v___x_2676_; 
v_val_2675_ = lean_ctor_get(v_t_x3f_2623_, 0);
lean_inc_n(v_val_2675_, 2);
lean_dec_ref_known(v_t_x3f_2623_, 1);
v___x_2676_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_val_2675_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___y_2679_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
if (v_a_2624_ == 0)
{
if (lean_obj_tag(v_h_x3f_2625_) == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2679_ = v___x_2716_;
goto v___jp_2678_;
}
else
{
lean_object* v_val_2717_; 
v_val_2717_ = lean_ctor_get(v_h_x3f_2625_, 0);
lean_inc(v_val_2717_);
lean_dec_ref_known(v_h_x3f_2625_, 1);
v___y_2679_ = v_val_2717_;
goto v___jp_2678_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2625_) == 0)
{
lean_object* v_toCold_2718_; lean_object* v_ref_2719_; lean_object* v_quotContext_2720_; lean_object* v_currMacroScope_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_toCold_2718_ = lean_ctor_get(v___y_2628_, 0);
v_ref_2719_ = lean_ctor_get(v___y_2628_, 2);
v_quotContext_2720_ = lean_ctor_get(v_toCold_2718_, 8);
v_currMacroScope_2721_ = lean_ctor_get(v_toCold_2718_, 9);
v___x_2722_ = 0;
v___x_2723_ = l_Lean_SourceInfo_fromRef(v_ref_2719_, v___x_2722_);
v___x_2724_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2725_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2723_, 12);
v___x_2726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2723_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2729_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2723_);
lean_ctor_set(v___x_2730_, 1, v___x_2728_);
lean_ctor_set(v___x_2730_, 2, v___x_2729_);
lean_inc_ref(v___x_2730_);
v___x_2731_ = l_Lean_Syntax_node1(v___x_2723_, v___x_2727_, v___x_2730_);
v___x_2732_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2733_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2734_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2735_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2736_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2737_ = lean_box(0);
lean_inc(v_currMacroScope_2721_);
lean_inc(v_quotContext_2720_);
v___x_2738_ = l_Lean_addMacroScope(v_quotContext_2720_, v___x_2737_, v_currMacroScope_2721_);
v___x_2739_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2740_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2723_);
lean_ctor_set(v___x_2740_, 1, v___x_2736_);
lean_ctor_set(v___x_2740_, 2, v___x_2738_);
lean_ctor_set(v___x_2740_, 3, v___x_2739_);
v___x_2741_ = l_Lean_Syntax_node1(v___x_2723_, v___x_2735_, v___x_2740_);
v___x_2742_ = l_Lean_Syntax_node1(v___x_2723_, v___x_2734_, v___x_2741_);
v___x_2743_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2744_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2723_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Lean_Syntax_node2(v___x_2723_, v___x_2743_, v___x_2745_, v_a_2677_);
v___x_2747_ = l_Lean_Syntax_node1(v___x_2723_, v___x_2728_, v___x_2746_);
v___x_2748_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2723_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l_Lean_Syntax_node5(v___x_2723_, v___x_2733_, v___x_2742_, v___x_2730_, v___x_2747_, v___x_2749_, v_a_2645_);
v___x_2751_ = l_Lean_Syntax_node1(v___x_2723_, v___x_2732_, v___x_2750_);
v___x_2752_ = l_Lean_Syntax_node3(v___x_2723_, v___x_2724_, v___x_2726_, v___x_2731_, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81);
v___x_2754_ = l_Lean_MessageData_ofExpr(v_val_2675_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Lean_MessageData_ofExpr(v_e_2622_);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v_fst_2632_ = v___x_2752_;
v_snd_2633_ = v___x_2759_;
goto v___jp_2631_;
}
else
{
lean_object* v_val_2760_; lean_object* v_ref_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_val_2760_ = lean_ctor_get(v_h_x3f_2625_, 0);
lean_inc_n(v_val_2760_, 2);
lean_dec_ref_known(v_h_x3f_2625_, 1);
v_ref_2761_ = lean_ctor_get(v___y_2628_, 2);
v___x_2762_ = 0;
v___x_2763_ = l_Lean_SourceInfo_fromRef(v_ref_2761_, v___x_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2765_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2763_, 10);
v___x_2766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2763_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2769_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2763_);
lean_ctor_set(v___x_2770_, 1, v___x_2768_);
lean_ctor_set(v___x_2770_, 2, v___x_2769_);
lean_inc_ref(v___x_2770_);
v___x_2771_ = l_Lean_Syntax_node1(v___x_2763_, v___x_2767_, v___x_2770_);
v___x_2772_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2773_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2774_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2775_ = l_Lean_mkIdent(v_val_2760_);
v___x_2776_ = l_Lean_Syntax_node1(v___x_2763_, v___x_2774_, v___x_2775_);
v___x_2777_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2778_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2763_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_Syntax_node2(v___x_2763_, v___x_2777_, v___x_2779_, v_a_2677_);
v___x_2781_ = l_Lean_Syntax_node1(v___x_2763_, v___x_2768_, v___x_2780_);
v___x_2782_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2763_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = l_Lean_Syntax_node5(v___x_2763_, v___x_2773_, v___x_2776_, v___x_2770_, v___x_2781_, v___x_2783_, v_a_2645_);
v___x_2785_ = l_Lean_Syntax_node1(v___x_2763_, v___x_2772_, v___x_2784_);
v___x_2786_ = l_Lean_Syntax_node3(v___x_2763_, v___x_2764_, v___x_2766_, v___x_2771_, v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2788_ = l_Lean_MessageData_ofName(v_val_2760_);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_MessageData_ofExpr(v_val_2675_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_MessageData_ofExpr(v_e_2622_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v_fst_2632_ = v___x_2786_;
v_snd_2633_ = v___x_2797_;
goto v___jp_2631_;
}
}
v___jp_2678_:
{
lean_object* v_ref_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_ref_2680_ = lean_ctor_get(v___y_2628_, 2);
v___x_2681_ = l_Lean_SourceInfo_fromRef(v_ref_2680_, v_a_2624_);
v___x_2682_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2683_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2681_, 10);
v___x_2684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2687_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2681_);
lean_ctor_set(v___x_2688_, 1, v___x_2686_);
lean_ctor_set(v___x_2688_, 2, v___x_2687_);
lean_inc_ref(v___x_2688_);
v___x_2689_ = l_Lean_Syntax_node1(v___x_2681_, v___x_2685_, v___x_2688_);
v___x_2690_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2691_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2692_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2679_);
v___x_2693_ = l_Lean_mkIdent(v___y_2679_);
v___x_2694_ = l_Lean_Syntax_node1(v___x_2681_, v___x_2692_, v___x_2693_);
v___x_2695_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2696_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2681_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_Syntax_node2(v___x_2681_, v___x_2695_, v___x_2697_, v_a_2677_);
v___x_2699_ = l_Lean_Syntax_node1(v___x_2681_, v___x_2686_, v___x_2698_);
v___x_2700_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2681_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_Syntax_node5(v___x_2681_, v___x_2691_, v___x_2694_, v___x_2688_, v___x_2699_, v___x_2701_, v_a_2645_);
v___x_2703_ = l_Lean_Syntax_node1(v___x_2681_, v___x_2690_, v___x_2702_);
v___x_2704_ = l_Lean_Syntax_node3(v___x_2681_, v___x_2682_, v___x_2684_, v___x_2689_, v___x_2703_);
v___x_2705_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2706_ = l_Lean_MessageData_ofName(v___y_2679_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_MessageData_ofExpr(v_val_2675_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_ofExpr(v_e_2622_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v_fst_2632_ = v___x_2704_;
v_snd_2633_ = v___x_2715_;
goto v___jp_2631_;
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v_val_2675_);
lean_dec(v_a_2645_);
lean_dec_ref(v___y_2628_);
lean_dec(v_h_x3f_2625_);
lean_dec_ref(v_e_2622_);
v_a_2798_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2676_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2676_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_dec(v_t_x3f_2623_);
if (v_a_2624_ == 0)
{
if (lean_obj_tag(v_h_x3f_2625_) == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2647_ = v___x_2806_;
goto v___jp_2646_;
}
else
{
lean_object* v_val_2807_; 
v_val_2807_ = lean_ctor_get(v_h_x3f_2625_, 0);
lean_inc(v_val_2807_);
lean_dec_ref_known(v_h_x3f_2625_, 1);
v___y_2647_ = v_val_2807_;
goto v___jp_2646_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2625_) == 0)
{
lean_object* v_toCold_2808_; lean_object* v_ref_2809_; lean_object* v_quotContext_2810_; lean_object* v_currMacroScope_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_toCold_2808_ = lean_ctor_get(v___y_2628_, 0);
v_ref_2809_ = lean_ctor_get(v___y_2628_, 2);
v_quotContext_2810_ = lean_ctor_get(v_toCold_2808_, 8);
v_currMacroScope_2811_ = lean_ctor_get(v_toCold_2808_, 9);
v___x_2812_ = 0;
v___x_2813_ = l_Lean_SourceInfo_fromRef(v_ref_2809_, v___x_2812_);
v___x_2814_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2815_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2813_, 9);
v___x_2816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2813_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2819_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2813_);
lean_ctor_set(v___x_2820_, 1, v___x_2818_);
lean_ctor_set(v___x_2820_, 2, v___x_2819_);
lean_inc_ref_n(v___x_2820_, 2);
v___x_2821_ = l_Lean_Syntax_node1(v___x_2813_, v___x_2817_, v___x_2820_);
v___x_2822_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2823_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2824_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2825_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2826_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2827_ = lean_box(0);
lean_inc(v_currMacroScope_2811_);
lean_inc(v_quotContext_2810_);
v___x_2828_ = l_Lean_addMacroScope(v_quotContext_2810_, v___x_2827_, v_currMacroScope_2811_);
v___x_2829_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2830_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2813_);
lean_ctor_set(v___x_2830_, 1, v___x_2826_);
lean_ctor_set(v___x_2830_, 2, v___x_2828_);
lean_ctor_set(v___x_2830_, 3, v___x_2829_);
v___x_2831_ = l_Lean_Syntax_node1(v___x_2813_, v___x_2825_, v___x_2830_);
v___x_2832_ = l_Lean_Syntax_node1(v___x_2813_, v___x_2824_, v___x_2831_);
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2813_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = l_Lean_Syntax_node5(v___x_2813_, v___x_2823_, v___x_2832_, v___x_2820_, v___x_2820_, v___x_2834_, v_a_2645_);
v___x_2836_ = l_Lean_Syntax_node1(v___x_2813_, v___x_2822_, v___x_2835_);
v___x_2837_ = l_Lean_Syntax_node3(v___x_2813_, v___x_2814_, v___x_2816_, v___x_2821_, v___x_2836_);
v___x_2838_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85);
v___x_2839_ = l_Lean_MessageData_ofExpr(v_e_2622_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v_fst_2632_ = v___x_2837_;
v_snd_2633_ = v___x_2840_;
goto v___jp_2631_;
}
else
{
lean_object* v_val_2841_; lean_object* v_ref_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_val_2841_ = lean_ctor_get(v_h_x3f_2625_, 0);
lean_inc_n(v_val_2841_, 2);
lean_dec_ref_known(v_h_x3f_2625_, 1);
v_ref_2842_ = lean_ctor_get(v___y_2628_, 2);
v___x_2843_ = 0;
v___x_2844_ = l_Lean_SourceInfo_fromRef(v_ref_2842_, v___x_2843_);
v___x_2845_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2846_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2844_, 7);
v___x_2847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2844_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2844_);
lean_ctor_set(v___x_2851_, 1, v___x_2849_);
lean_ctor_set(v___x_2851_, 2, v___x_2850_);
lean_inc_ref_n(v___x_2851_, 2);
v___x_2852_ = l_Lean_Syntax_node1(v___x_2844_, v___x_2848_, v___x_2851_);
v___x_2853_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2854_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2855_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2856_ = l_Lean_mkIdent(v_val_2841_);
v___x_2857_ = l_Lean_Syntax_node1(v___x_2844_, v___x_2855_, v___x_2856_);
v___x_2858_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2844_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = l_Lean_Syntax_node5(v___x_2844_, v___x_2854_, v___x_2857_, v___x_2851_, v___x_2851_, v___x_2859_, v_a_2645_);
v___x_2861_ = l_Lean_Syntax_node1(v___x_2844_, v___x_2853_, v___x_2860_);
v___x_2862_ = l_Lean_Syntax_node3(v___x_2844_, v___x_2845_, v___x_2847_, v___x_2852_, v___x_2861_);
v___x_2863_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2864_ = l_Lean_MessageData_ofName(v_val_2841_);
v___x_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_MessageData_ofExpr(v_e_2622_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v_fst_2632_ = v___x_2862_;
v_snd_2633_ = v___x_2869_;
goto v___jp_2631_;
}
}
}
v___jp_2646_:
{
lean_object* v_ref_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_ref_2648_ = lean_ctor_get(v___y_2628_, 2);
v___x_2649_ = l_Lean_SourceInfo_fromRef(v_ref_2648_, v_a_2624_);
v___x_2650_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2651_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2649_, 7);
v___x_2652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2655_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2649_);
lean_ctor_set(v___x_2656_, 1, v___x_2654_);
lean_ctor_set(v___x_2656_, 2, v___x_2655_);
lean_inc_ref_n(v___x_2656_, 2);
v___x_2657_ = l_Lean_Syntax_node1(v___x_2649_, v___x_2653_, v___x_2656_);
v___x_2658_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2659_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2660_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2647_);
v___x_2661_ = l_Lean_mkIdent(v___y_2647_);
v___x_2662_ = l_Lean_Syntax_node1(v___x_2649_, v___x_2660_, v___x_2661_);
v___x_2663_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2649_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_Syntax_node5(v___x_2649_, v___x_2659_, v___x_2662_, v___x_2656_, v___x_2656_, v___x_2664_, v_a_2645_);
v___x_2666_ = l_Lean_Syntax_node1(v___x_2649_, v___x_2658_, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node3(v___x_2649_, v___x_2650_, v___x_2652_, v___x_2657_, v___x_2666_);
v___x_2668_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2669_ = l_Lean_MessageData_ofName(v___y_2647_);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofExpr(v_e_2622_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v_fst_2632_ = v___x_2667_;
v_snd_2633_ = v___x_2674_;
goto v___jp_2631_;
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v___y_2628_);
lean_dec(v_h_x3f_2625_);
lean_dec(v_t_x3f_2623_);
lean_dec_ref(v_e_2622_);
v_a_2870_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2644_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2644_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
v___jp_2631_:
{
lean_object* v___x_2634_; lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v___x_2634_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_snd_2633_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec_ref(v___y_2628_);
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_fst_2632_);
lean_ctor_set(v___x_2639_, 1, v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2639_);
v___x_2641_ = v___x_2637_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object* v_e_2878_, lean_object* v_t_x3f_2879_, lean_object* v_a_2880_, lean_object* v_h_x3f_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v_a_16933__boxed_2887_; lean_object* v_res_2888_; 
v_a_16933__boxed_2887_ = lean_unbox(v_a_2880_);
v_res_2888_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(v_e_2878_, v_t_x3f_2879_, v_a_16933__boxed_2887_, v_h_x3f_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2888_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1));
v___x_2893_ = l_Lean_MessageData_ofFormat(v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* v_ref_2894_, lean_object* v_h_x3f_2895_, lean_object* v_t_x3f_2896_, lean_object* v_e_2897_, lean_object* v_origSpan_x3f_2898_, lean_object* v_checkState_x3f_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_tac_2910_; lean_object* v_msg_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___x_2923_; 
lean_inc(v_a_2907_);
lean_inc_ref(v_a_2906_);
lean_inc(v_a_2905_);
lean_inc_ref(v_a_2904_);
lean_inc_ref(v_e_2897_);
v___x_2923_ = lean_infer_type(v_e_2897_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = l_Lean_Meta_isProp(v_a_2924_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___f_2927_; lean_object* v___x_2928_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___f_2927_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2927_, 0, v_e_2897_);
lean_closure_set(v___f_2927_, 1, v_t_x3f_2896_);
lean_closure_set(v___f_2927_, 2, v_a_2926_);
lean_closure_set(v___f_2927_, 3, v_h_x3f_2895_);
v___x_2928_ = l_Lean_Meta_withExposedNames___redArg(v___f_2927_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
if (lean_obj_tag(v_checkState_x3f_2899_) == 1)
{
lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v_val_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_fst_2930_ = lean_ctor_get(v_a_2929_, 0);
lean_inc(v_fst_2930_);
v_snd_2931_ = lean_ctor_get(v_a_2929_, 1);
lean_inc_n(v_snd_2931_, 2);
lean_dec(v_a_2929_);
v_val_2932_ = lean_ctor_get(v_checkState_x3f_2899_, 0);
lean_inc(v_val_2932_);
lean_dec_ref_known(v_checkState_x3f_2899_, 1);
v___x_2933_ = lean_box(0);
v___x_2934_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_2930_, v_snd_2931_, v_val_2932_, v___x_2933_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
if (lean_obj_tag(v_a_2935_) == 1)
{
lean_object* v_val_2936_; lean_object* v_fst_2937_; lean_object* v_snd_2938_; 
lean_dec(v_snd_2931_);
v_val_2936_ = lean_ctor_get(v_a_2935_, 0);
lean_inc(v_val_2936_);
lean_dec_ref_known(v_a_2935_, 1);
v_fst_2937_ = lean_ctor_get(v_val_2936_, 0);
lean_inc(v_fst_2937_);
v_snd_2938_ = lean_ctor_get(v_val_2936_, 1);
lean_inc(v_snd_2938_);
lean_dec(v_val_2936_);
v_tac_2910_ = v_fst_2937_;
v_msg_2911_ = v_snd_2938_;
v___y_2912_ = v_a_2906_;
v___y_2913_ = v_a_2907_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v_a_2935_);
lean_dec(v_origSpan_x3f_2898_);
lean_dec(v_ref_2894_);
v___x_2939_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
v___x_2940_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_2939_, v_snd_2931_);
v___x_2941_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_2940_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2949_; 
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
lean_object* v_unused_2950_; 
v_unused_2950_ = lean_ctor_get(v___x_2941_, 0);
lean_dec(v_unused_2950_);
v___x_2943_ = v___x_2941_;
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
else
{
lean_dec(v___x_2941_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = lean_box(0);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
return v___x_2941_;
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec(v_snd_2931_);
lean_dec(v_origSpan_x3f_2898_);
lean_dec(v_ref_2894_);
v_a_2951_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2934_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2934_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_fst_2959_; lean_object* v_snd_2960_; 
lean_dec(v_checkState_x3f_2899_);
v_fst_2959_ = lean_ctor_get(v_a_2929_, 0);
lean_inc(v_fst_2959_);
v_snd_2960_ = lean_ctor_get(v_a_2929_, 1);
lean_inc(v_snd_2960_);
lean_dec(v_a_2929_);
v_tac_2910_ = v_fst_2959_;
v_msg_2911_ = v_snd_2960_;
v___y_2912_ = v_a_2906_;
v___y_2913_ = v_a_2907_;
goto v___jp_2909_;
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_checkState_x3f_2899_);
lean_dec(v_origSpan_x3f_2898_);
lean_dec(v_ref_2894_);
v_a_2961_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2928_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2928_);
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
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_checkState_x3f_2899_);
lean_dec(v_origSpan_x3f_2898_);
lean_dec_ref(v_e_2897_);
lean_dec(v_t_x3f_2896_);
lean_dec(v_h_x3f_2895_);
lean_dec(v_ref_2894_);
v_a_2969_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2925_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2925_);
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
lean_dec(v_checkState_x3f_2899_);
lean_dec(v_origSpan_x3f_2898_);
lean_dec_ref(v_e_2897_);
lean_dec(v_t_x3f_2896_);
lean_dec(v_h_x3f_2895_);
lean_dec(v_ref_2894_);
v_a_2977_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2923_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2923_);
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
v___jp_2909_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v_tac_2910_);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_msg_2911_);
v___x_2918_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2915_);
lean_ctor_set(v___x_2918_, 1, v___x_2916_);
lean_ctor_set(v___x_2918_, 2, v___x_2916_);
lean_ctor_set(v___x_2918_, 3, v___x_2916_);
lean_ctor_set(v___x_2918_, 4, v___x_2917_);
lean_ctor_set(v___x_2918_, 5, v___x_2916_);
v___x_2919_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_2920_ = 4;
v___x_2921_ = l_Lean_MessageData_nil;
v___x_2922_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2894_, v___x_2918_, v_origSpan_x3f_2898_, v___x_2919_, v___x_2916_, v___x_2920_, v___x_2921_, v___y_2912_, v___y_2913_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object* v_ref_2985_, lean_object* v_h_x3f_2986_, lean_object* v_t_x3f_2987_, lean_object* v_e_2988_, lean_object* v_origSpan_x3f_2989_, lean_object* v_checkState_x3f_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(v_ref_2985_, v_h_x3f_2986_, v_t_x3f_2987_, v_e_2988_, v_origSpan_x3f_2989_, v_checkState_x3f_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
if (lean_obj_tag(v_a_3002_) == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = l_List_reverse___redArg(v_a_3003_);
return v___x_3004_;
}
else
{
lean_object* v_head_3005_; lean_object* v_tail_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3038_; 
v_head_3005_ = lean_ctor_get(v_a_3002_, 0);
v_tail_3006_ = lean_ctor_get(v_a_3002_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_3002_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3008_ = v_a_3002_;
v_isShared_3009_ = v_isSharedCheck_3038_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_tail_3006_);
lean_inc(v_head_3005_);
lean_dec(v_a_3002_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3038_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___y_3011_; lean_object* v_fst_3016_; lean_object* v_snd_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3037_; 
v_fst_3016_ = lean_ctor_get(v_head_3005_, 0);
v_snd_3017_ = lean_ctor_get(v_head_3005_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_head_3005_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3019_ = v_head_3005_;
v_isShared_3020_ = v_isSharedCheck_3037_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_snd_3017_);
lean_inc(v_fst_3016_);
lean_dec(v_head_3005_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3037_;
goto v_resetjp_3018_;
}
v___jp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v_a_3003_);
lean_ctor_set(v___x_3008_, 0, v___y_3011_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___y_3011_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_a_3003_);
v___x_3013_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
v_a_3002_ = v_tail_3006_;
v_a_3003_ = v___x_3013_;
goto _start;
}
}
v_resetjp_3018_:
{
lean_object* v___y_3022_; uint8_t v___x_3034_; 
v___x_3034_ = lean_unbox(v_snd_3017_);
lean_dec(v_snd_3017_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_3022_ = v___x_3035_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3036_; 
v___x_3036_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0));
v___y_3022_ = v___x_3036_;
goto v___jp_3021_;
}
v___jp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
lean_inc_ref(v___y_3022_);
v___x_3023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___y_3022_);
v___x_3024_ = l_Lean_MessageData_ofFormat(v___x_3023_);
v___x_3025_ = l_Lean_Expr_isConst(v_fst_3016_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3026_ = l_Lean_MessageData_ofExpr(v_fst_3016_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 7);
lean_ctor_set(v___x_3019_, 1, v___x_3026_);
lean_ctor_set(v___x_3019_, 0, v___x_3024_);
v___x_3028_ = v___x_3019_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
v___y_3011_ = v___x_3028_;
goto v___jp_3010_;
}
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3030_ = l_Lean_MessageData_ofConst(v_fst_3016_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 7);
lean_ctor_set(v___x_3019_, 1, v___x_3030_);
lean_ctor_set(v___x_3019_, 0, v___x_3024_);
v___x_3032_ = v___x_3019_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
v___y_3011_ = v___x_3032_;
goto v___jp_3010_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t v_sz_3046_, size_t v_i_3047_, lean_object* v_bs_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
uint8_t v___x_3054_; 
v___x_3054_ = lean_usize_dec_lt(v_i_3047_, v_sz_3046_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_bs_3048_);
return v___x_3055_;
}
else
{
lean_object* v_v_3056_; lean_object* v_fst_3057_; lean_object* v_snd_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3101_; 
v_v_3056_ = lean_array_uget(v_bs_3048_, v_i_3047_);
v_fst_3057_ = lean_ctor_get(v_v_3056_, 0);
v_snd_3058_ = lean_ctor_get(v_v_3056_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_v_3056_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3060_ = v_v_3056_;
v_isShared_3061_ = v_isSharedCheck_3101_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_snd_3058_);
lean_inc(v_fst_3057_);
lean_dec(v_v_3056_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3101_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v_bs_x27_3063_; lean_object* v_a_3065_; lean_object* v___x_3070_; 
v___x_3062_ = lean_unsigned_to_nat(0u);
v_bs_x27_3063_ = lean_array_uset(v_bs_3048_, v_i_3047_, v___x_3062_);
v___x_3070_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_fst_3057_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3070_) == 0)
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_unbox(v_snd_3058_);
if (v___x_3071_ == 0)
{
lean_object* v_a_3072_; lean_object* v_ref_3073_; uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_del_object(v___x_3060_);
v_a_3072_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3070_, 1);
v_ref_3073_ = lean_ctor_get(v___y_3051_, 2);
v___x_3074_ = lean_unbox(v_snd_3058_);
lean_dec(v_snd_3058_);
v___x_3075_ = l_Lean_SourceInfo_fromRef(v_ref_3073_, v___x_3074_);
v___x_3076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3078_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
lean_inc(v___x_3075_);
v___x_3079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3075_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
lean_ctor_set(v___x_3079_, 2, v___x_3078_);
v___x_3080_ = l_Lean_Syntax_node2(v___x_3075_, v___x_3076_, v___x_3079_, v_a_3072_);
v_a_3065_ = v___x_3080_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3081_; lean_object* v_ref_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
lean_dec(v_snd_3058_);
v_a_3081_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3070_, 1);
v_ref_3082_ = lean_ctor_get(v___y_3051_, 2);
v___x_3083_ = 0;
v___x_3084_ = l_Lean_SourceInfo_fromRef(v_ref_3082_, v___x_3083_);
v___x_3085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2));
lean_inc(v___x_3084_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set_tag(v___x_3060_, 2);
lean_ctor_set(v___x_3060_, 1, v___x_3087_);
lean_ctor_set(v___x_3060_, 0, v___x_3084_);
v___x_3089_ = v___x_3060_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_inc(v___x_3084_);
v___x_3090_ = l_Lean_Syntax_node1(v___x_3084_, v___x_3086_, v___x_3089_);
v___x_3091_ = l_Lean_Syntax_node2(v___x_3084_, v___x_3085_, v___x_3090_, v_a_3081_);
v_a_3065_ = v___x_3091_;
goto v___jp_3064_;
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v_bs_x27_3063_);
lean_del_object(v___x_3060_);
lean_dec(v_snd_3058_);
v_a_3093_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3070_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3070_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
v___jp_3064_:
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((size_t)1ULL);
v___x_3067_ = lean_usize_add(v_i_3047_, v___x_3066_);
v___x_3068_ = lean_array_uset(v_bs_x27_3063_, v_i_3047_, v_a_3065_);
v_i_3047_ = v___x_3067_;
v_bs_3048_ = v___x_3068_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object* v_sz_3102_, lean_object* v_i_3103_, lean_object* v_bs_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
size_t v_sz_boxed_3110_; size_t v_i_boxed_3111_; lean_object* v_res_3112_; 
v_sz_boxed_3110_ = lean_unbox_usize(v_sz_3102_);
lean_dec(v_sz_3102_);
v_i_boxed_3111_ = lean_unbox_usize(v_i_3103_);
lean_dec(v_i_3103_);
v_res_3112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_boxed_3110_, v_i_boxed_3111_, v_bs_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3112_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0));
v___x_3115_ = l_Lean_stringToMessageData(v___x_3114_);
return v___x_3115_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2));
v___x_3118_ = l_Lean_stringToMessageData(v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_3120_ = l_Lean_stringToMessageData(v___x_3119_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6));
v___x_3125_ = l_Lean_MessageData_ofFormat(v___x_3124_);
return v___x_3125_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8));
v___x_3128_ = l_Lean_stringToMessageData(v___x_3127_);
return v___x_3128_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10));
v___x_3131_ = l_Lean_stringToMessageData(v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object* v_type_x3f_3169_, lean_object* v_rules_3170_, lean_object* v_loc_x3f_3171_, lean_object* v___x_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v_extraMsg_3181_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; size_t v_sz_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v_sz_3226_ = lean_array_size(v___x_3172_);
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_3226_, v___x_3227_, v___x_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_a_3233_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12));
v___x_3231_ = l_Lean_Syntax_SepArray_ofElems(v___x_3230_, v_a_3229_);
lean_dec(v_a_3229_);
if (lean_obj_tag(v_loc_x3f_3171_) == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_box(0);
v_a_3233_ = v___x_3257_;
goto v___jp_3232_;
}
else
{
lean_object* v_val_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_val_3258_ = lean_ctor_get(v_loc_x3f_3171_, 0);
v___x_3259_ = lean_box(1);
lean_inc(v_val_3258_);
v___x_3260_ = l_Lean_PrettyPrinter_delab(v_val_3258_, v___x_3259_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v_ref_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v_ref_3262_ = lean_ctor_get(v___y_3175_, 2);
v___x_3263_ = 0;
v___x_3264_ = l_Lean_SourceInfo_fromRef(v_ref_3262_, v___x_3263_);
v___x_3265_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24));
v___x_3266_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25));
lean_inc_n(v___x_3264_, 3);
v___x_3267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3264_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27));
v___x_3269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3270_ = l_Lean_Syntax_node1(v___x_3264_, v___x_3269_, v_a_3261_);
v___x_3271_ = l_Lean_Syntax_node1(v___x_3264_, v___x_3268_, v___x_3270_);
v___x_3272_ = l_Lean_Syntax_node2(v___x_3264_, v___x_3265_, v___x_3267_, v___x_3271_);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
v_a_3233_ = v___x_3273_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref_known(v_loc_x3f_3171_, 1);
lean_dec_ref(v___x_3231_);
lean_dec(v_rules_3170_);
lean_dec(v_type_x3f_3169_);
v_a_3274_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3260_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3260_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
v___jp_3232_:
{
lean_object* v_ref_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_ref_3234_ = lean_ctor_get(v___y_3175_, 2);
v___x_3235_ = 0;
v___x_3236_ = l_Lean_SourceInfo_fromRef(v_ref_3234_, v___x_3235_);
v___x_3237_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14));
v___x_3238_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15));
lean_inc_n(v___x_3236_, 7);
v___x_3239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3236_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17));
v___x_3241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3242_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_3243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3236_);
lean_ctor_set(v___x_3243_, 1, v___x_3241_);
lean_ctor_set(v___x_3243_, 2, v___x_3242_);
v___x_3244_ = l_Lean_Syntax_node1(v___x_3236_, v___x_3240_, v___x_3243_);
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19));
v___x_3246_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20));
v___x_3247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3236_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Array_append___redArg(v___x_3242_, v___x_3231_);
lean_dec_ref(v___x_3231_);
v___x_3249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3236_);
lean_ctor_set(v___x_3249_, 1, v___x_3241_);
lean_ctor_set(v___x_3249_, 2, v___x_3248_);
v___x_3250_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21));
v___x_3251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3236_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_Syntax_node3(v___x_3236_, v___x_3245_, v___x_3247_, v___x_3249_, v___x_3251_);
if (lean_obj_tag(v_a_3233_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___y_3201_ = v___x_3244_;
v___y_3202_ = v___x_3236_;
v___y_3203_ = v___x_3239_;
v___y_3204_ = v___x_3252_;
v___y_3205_ = v___x_3237_;
v___y_3206_ = v___x_3241_;
v___y_3207_ = v___x_3242_;
v___y_3208_ = v___x_3253_;
goto v___jp_3200_;
}
else
{
lean_object* v_val_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_val_3254_ = lean_ctor_get(v_a_3233_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v_a_3233_, 1);
v___x_3255_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___x_3256_ = lean_array_push(v___x_3255_, v_val_3254_);
v___y_3201_ = v___x_3244_;
v___y_3202_ = v___x_3236_;
v___y_3203_ = v___x_3239_;
v___y_3204_ = v___x_3252_;
v___y_3205_ = v___x_3237_;
v___y_3206_ = v___x_3241_;
v___y_3207_ = v___x_3242_;
v___y_3208_ = v___x_3256_;
goto v___jp_3200_;
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_loc_x3f_3171_);
lean_dec(v_rules_3170_);
lean_dec(v_type_x3f_3169_);
v_a_3282_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3228_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3228_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
v___jp_3178_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___y_3180_);
lean_ctor_set(v___x_3182_, 1, v_extraMsg_3181_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___y_3179_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
v___jp_3185_:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___y_3187_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
switch(lean_obj_tag(v_type_x3f_3169_))
{
case 0:
{
lean_object* v_a_3189_; lean_object* v___x_3190_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___x_3188_);
v___x_3190_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1);
v___y_3179_ = v___y_3186_;
v___y_3180_ = v_a_3189_;
v_extraMsg_3181_ = v___x_3190_;
goto v___jp_3178_;
}
case 1:
{
lean_object* v_a_3191_; lean_object* v_a_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v_a_3197_; 
v_a_3191_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3188_);
v_a_3192_ = lean_ctor_get(v_type_x3f_3169_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v_type_x3f_3169_, 1);
v___x_3193_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3);
v___x_3194_ = l_Lean_MessageData_ofExpr(v_a_3192_);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_3195_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref(v___x_3196_);
v___y_3179_ = v___y_3186_;
v___y_3180_ = v_a_3191_;
v_extraMsg_3181_ = v_a_3197_;
goto v___jp_3178_;
}
default: 
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3188_);
v___x_3199_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4);
v___y_3179_ = v___y_3186_;
v___y_3180_ = v_a_3198_;
v_extraMsg_3181_ = v___x_3199_;
goto v___jp_3178_;
}
}
}
v___jp_3200_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3209_ = l_Array_append___redArg(v___y_3207_, v___y_3208_);
lean_dec_ref(v___y_3208_);
lean_inc(v___y_3206_);
lean_inc(v___y_3202_);
v___x_3210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3210_, 0, v___y_3202_);
lean_ctor_set(v___x_3210_, 1, v___y_3206_);
lean_ctor_set(v___x_3210_, 2, v___x_3209_);
lean_inc(v___y_3205_);
v___x_3211_ = l_Lean_Syntax_node4(v___y_3202_, v___y_3205_, v___y_3203_, v___y_3201_, v___y_3204_, v___x_3210_);
v___x_3212_ = lean_box(0);
v___x_3213_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(v_rules_3170_, v___x_3212_);
v___x_3214_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7);
v___x_3215_ = l_Lean_MessageData_joinSep(v___x_3213_, v___x_3214_);
v___x_3216_ = l_Lean_MessageData_sbracket(v___x_3215_);
if (lean_obj_tag(v_loc_x3f_3171_) == 1)
{
lean_object* v_val_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_val_3217_ = lean_ctor_get(v_loc_x3f_3171_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v_loc_x3f_3171_, 1);
v___x_3218_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v___x_3216_);
v___x_3220_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11);
v___x_3221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Lean_MessageData_ofExpr(v_val_3217_);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___y_3186_ = v___x_3211_;
v___y_3187_ = v___x_3223_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec(v_loc_x3f_3171_);
v___x_3224_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3216_);
v___y_3186_ = v___x_3211_;
v___y_3187_ = v___x_3225_;
goto v___jp_3185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(lean_object* v_type_x3f_3290_, lean_object* v_rules_3291_, lean_object* v_loc_x3f_3292_, lean_object* v___x_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(v_type_x3f_3290_, v_rules_3291_, v_loc_x3f_3292_, v___x_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
return v_res_3299_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1));
v___x_3304_ = l_Lean_MessageData_ofFormat(v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* v_ref_3305_, lean_object* v_rules_3306_, lean_object* v_type_x3f_3307_, lean_object* v_loc_x3f_3308_, lean_object* v_origSpan_x3f_3309_, lean_object* v_checkState_x3f_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v___f_3321_; lean_object* v___x_3322_; 
lean_inc(v_rules_3306_);
v___x_3320_ = lean_array_mk(v_rules_3306_);
lean_inc(v_type_x3f_3307_);
v___f_3321_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3321_, 0, v_type_x3f_3307_);
lean_closure_set(v___f_3321_, 1, v_rules_3306_);
lean_closure_set(v___f_3321_, 2, v_loc_x3f_3308_);
lean_closure_set(v___f_3321_, 3, v___x_3320_);
v___x_3322_ = l_Lean_Meta_withExposedNames___redArg(v___f_3321_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v_snd_3324_; lean_object* v_fst_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3396_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v_snd_3324_ = lean_ctor_get(v_a_3323_, 1);
v_fst_3325_ = lean_ctor_get(v_a_3323_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3323_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3327_ = v_a_3323_;
v_isShared_3328_ = v_isSharedCheck_3396_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_snd_3324_);
lean_inc(v_fst_3325_);
lean_dec(v_a_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3396_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_fst_3329_; lean_object* v_snd_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3395_; 
v_fst_3329_ = lean_ctor_get(v_snd_3324_, 0);
v_snd_3330_ = lean_ctor_get(v_snd_3324_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_snd_3324_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3332_ = v_snd_3324_;
v_isShared_3333_ = v_isSharedCheck_3395_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_snd_3330_);
lean_inc(v_fst_3329_);
lean_dec(v_snd_3324_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3395_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_tac_3335_; lean_object* v_tacMsg_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; 
if (lean_obj_tag(v_checkState_x3f_3310_) == 1)
{
lean_object* v_val_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3394_; 
v_val_3353_ = lean_ctor_get(v_checkState_x3f_3310_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_checkState_x3f_3310_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3355_ = v_checkState_x3f_3310_;
v_isShared_3356_ = v_isSharedCheck_3394_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_val_3353_);
lean_dec(v_checkState_x3f_3310_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3394_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___y_3358_; 
if (lean_obj_tag(v_type_x3f_3307_) == 1)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; 
v_a_3389_ = lean_ctor_get(v_type_x3f_3307_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v_type_x3f_3307_, 1);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v_a_3389_);
v___x_3391_ = v___x_3355_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v___y_3358_ = v___x_3391_;
goto v___jp_3357_;
}
}
else
{
lean_object* v___x_3393_; 
lean_del_object(v___x_3355_);
lean_dec(v_type_x3f_3307_);
v___x_3393_ = lean_box(0);
v___y_3358_ = v___x_3393_;
goto v___jp_3357_;
}
v___jp_3357_:
{
lean_object* v___x_3359_; 
lean_inc(v_fst_3329_);
v___x_3359_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_3325_, v_fst_3329_, v_val_3353_, v___y_3358_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
if (lean_obj_tag(v_a_3360_) == 1)
{
lean_object* v_val_3361_; lean_object* v_fst_3362_; lean_object* v_snd_3363_; 
lean_dec(v_fst_3329_);
v_val_3361_ = lean_ctor_get(v_a_3360_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v_a_3360_, 1);
v_fst_3362_ = lean_ctor_get(v_val_3361_, 0);
lean_inc(v_fst_3362_);
v_snd_3363_ = lean_ctor_get(v_val_3361_, 1);
lean_inc(v_snd_3363_);
lean_dec(v_val_3361_);
v_tac_3335_ = v_fst_3362_;
v_tacMsg_3336_ = v_snd_3363_;
v___y_3337_ = v_a_3317_;
v___y_3338_ = v_a_3318_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
lean_dec(v_a_3360_);
lean_del_object(v___x_3332_);
lean_del_object(v___x_3327_);
lean_dec(v_origSpan_x3f_3309_);
lean_dec(v_ref_3305_);
v___x_3364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v_fst_3329_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v_snd_3330_);
v___x_3370_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_3368_, v___x_3369_);
v___x_3371_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_3370_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3379_; 
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v___x_3371_, 0);
lean_dec(v_unused_3380_);
v___x_3373_ = v___x_3371_;
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v___x_3371_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_box(0);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
else
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_del_object(v___x_3332_);
lean_dec(v_snd_3330_);
lean_dec(v_fst_3329_);
lean_del_object(v___x_3327_);
lean_dec(v_origSpan_x3f_3309_);
lean_dec(v_ref_3305_);
v_a_3381_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3359_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3359_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
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
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
}
else
{
lean_dec(v_checkState_x3f_3310_);
lean_dec(v_type_x3f_3307_);
v_tac_3335_ = v_fst_3325_;
v_tacMsg_3336_ = v_fst_3329_;
v___y_3337_ = v_a_3317_;
v___y_3338_ = v_a_3318_;
goto v___jp_3334_;
}
v___jp_3334_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v_tac_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3339_);
v___x_3341_ = v___x_3332_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_tac_3335_);
v___x_3341_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3342_ = lean_box(0);
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 7);
lean_ctor_set(v___x_3327_, 1, v_snd_3330_);
lean_ctor_set(v___x_3327_, 0, v_tacMsg_3336_);
v___x_3344_ = v___x_3327_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_tacMsg_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_snd_3330_);
v___x_3344_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
v___x_3346_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3341_);
lean_ctor_set(v___x_3346_, 1, v___x_3342_);
lean_ctor_set(v___x_3346_, 2, v___x_3342_);
lean_ctor_set(v___x_3346_, 3, v___x_3342_);
lean_ctor_set(v___x_3346_, 4, v___x_3345_);
lean_ctor_set(v___x_3346_, 5, v___x_3342_);
v___x_3347_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_3348_ = 4;
v___x_3349_ = l_Lean_MessageData_nil;
v___x_3350_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3305_, v___x_3346_, v_origSpan_x3f_3309_, v___x_3347_, v___x_3342_, v___x_3348_, v___x_3349_, v___y_3337_, v___y_3338_);
return v___x_3350_;
}
}
}
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_checkState_x3f_3310_);
lean_dec(v_origSpan_x3f_3309_);
lean_dec(v_type_x3f_3307_);
lean_dec(v_ref_3305_);
v_a_3397_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3322_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3322_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object* v_ref_3405_, lean_object* v_rules_3406_, lean_object* v_type_x3f_3407_, lean_object* v_loc_x3f_3408_, lean_object* v_origSpan_x3f_3409_, lean_object* v_checkState_x3f_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3405_, v_rules_3406_, v_type_x3f_3407_, v_loc_x3f_3408_, v_origSpan_x3f_3409_, v_checkState_x3f_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
return v_res_3420_;
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
