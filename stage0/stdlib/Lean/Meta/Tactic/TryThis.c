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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_pp_mvars_anonymous;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Lean_Meta_withExposedNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Meta_Hint_textInsertionWidget;
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\n-- Remaining subgoals:"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4;
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
lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_116_; 
v___x_103_ = l_Lean_Server_RequestM_readDoc___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(v_a_101_);
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_116_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_116_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_116_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_108_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
v___f_109_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed), 6, 3);
lean_closure_set(v___f_109_, 0, v___x_108_);
lean_closure_set(v___f_109_, 1, v_a_104_);
lean_closure_set(v___f_109_, 2, v_params_99_);
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___closed__0));
v___x_111_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_100_);
v___x_112_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_109_, v___x_110_, v___x_111_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_112_);
v___x_114_ = v___x_106_;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(lean_object* v_opts_165_, lean_object* v_opt_166_){
_start:
{
lean_object* v_name_167_; lean_object* v_defValue_168_; lean_object* v_map_169_; lean_object* v___x_170_; 
v_name_167_ = lean_ctor_get(v_opt_166_, 0);
v_defValue_168_ = lean_ctor_get(v_opt_166_, 1);
v_map_169_ = lean_ctor_get(v_opts_165_, 0);
v___x_170_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_169_, v_name_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
uint8_t v___x_171_; 
v___x_171_ = lean_unbox(v_defValue_168_);
return v___x_171_;
}
else
{
lean_object* v_val_172_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v___x_170_, 1);
if (lean_obj_tag(v_val_172_) == 1)
{
uint8_t v_v_173_; 
v_v_173_ = lean_ctor_get_uint8(v_val_172_, 0);
lean_dec_ref_known(v_val_172_, 0);
return v_v_173_;
}
else
{
uint8_t v___x_174_; 
lean_dec(v_val_172_);
v___x_174_ = lean_unbox(v_defValue_168_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1___boxed(lean_object* v_opts_175_, lean_object* v_opt_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_opts_175_, v_opt_176_);
lean_dec_ref(v_opt_176_);
lean_dec_ref(v_opts_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(lean_object* v_opts_179_, lean_object* v_opt_180_){
_start:
{
lean_object* v_name_181_; lean_object* v_defValue_182_; lean_object* v_map_183_; lean_object* v___x_184_; 
v_name_181_ = lean_ctor_get(v_opt_180_, 0);
v_defValue_182_ = lean_ctor_get(v_opt_180_, 1);
v_map_183_ = lean_ctor_get(v_opts_179_, 0);
v___x_184_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_183_, v_name_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_inc(v_defValue_182_);
return v_defValue_182_;
}
else
{
lean_object* v_val_185_; 
v_val_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v___x_184_, 1);
if (lean_obj_tag(v_val_185_) == 3)
{
lean_object* v_v_186_; 
v_v_186_ = lean_ctor_get(v_val_185_, 0);
lean_inc(v_v_186_);
lean_dec_ref_known(v_val_185_, 1);
return v_v_186_;
}
else
{
lean_dec(v_val_185_);
lean_inc(v_defValue_182_);
return v_defValue_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2___boxed(lean_object* v_opts_187_, lean_object* v_opt_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v_opts_187_, v_opt_188_);
lean_dec_ref(v_opt_188_);
lean_dec_ref(v_opts_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(lean_object* v_o_193_, lean_object* v_k_194_, uint8_t v_v_195_){
_start:
{
lean_object* v_map_196_; uint8_t v_hasTrace_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_211_; 
v_map_196_ = lean_ctor_get(v_o_193_, 0);
v_hasTrace_197_ = lean_ctor_get_uint8(v_o_193_, sizeof(void*)*1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_o_193_);
if (v_isSharedCheck_211_ == 0)
{
v___x_199_ = v_o_193_;
v_isShared_200_ = v_isSharedCheck_211_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_map_196_);
lean_dec(v_o_193_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_211_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_201_, 0, v_v_195_);
lean_inc(v_k_194_);
v___x_202_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_194_, v___x_201_, v_map_196_);
if (v_hasTrace_197_ == 0)
{
lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_206_; 
v___x_203_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__1));
v___x_204_ = l_Lean_Name_isPrefixOf(v___x_203_, v_k_194_);
lean_dec(v_k_194_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_202_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_204_);
return v___x_206_;
}
}
else
{
lean_object* v___x_209_; 
lean_dec(v_k_194_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_209_ = v___x_199_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_210_, sizeof(void*)*1, v_hasTrace_197_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___boxed(lean_object* v_o_212_, lean_object* v_k_213_, lean_object* v_v_214_){
_start:
{
uint8_t v_v_boxed_215_; lean_object* v_res_216_; 
v_v_boxed_215_ = lean_unbox(v_v_214_);
v_res_216_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(v_o_212_, v_k_213_, v_v_boxed_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(lean_object* v_opts_217_, lean_object* v_opt_218_, uint8_t v_val_219_){
_start:
{
lean_object* v_name_220_; lean_object* v___x_221_; 
v_name_220_ = lean_ctor_get(v_opt_218_, 0);
lean_inc(v_name_220_);
lean_dec_ref(v_opt_218_);
v___x_221_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0(v_opts_217_, v_name_220_, v_val_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0___boxed(lean_object* v_opts_222_, lean_object* v_opt_223_, lean_object* v_val_224_){
_start:
{
uint8_t v_val_boxed_225_; lean_object* v_res_226_; 
v_val_boxed_225_ = lean_unbox(v_val_224_);
v_res_226_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_opts_222_, v_opt_223_, v_val_boxed_225_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object* v_e_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; lean_object* v_fileName_239_; lean_object* v_fileMap_240_; lean_object* v_options_241_; lean_object* v_currRecDepth_242_; lean_object* v_ref_243_; lean_object* v_currNamespace_244_; lean_object* v_openDecls_245_; lean_object* v_initHeartbeats_246_; lean_object* v_maxHeartbeats_247_; lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_cancelTk_x3f_250_; uint8_t v_suppressElabErrors_251_; lean_object* v_inheritedTraceOptions_252_; lean_object* v_env_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v_fileName_261_; lean_object* v_fileMap_262_; lean_object* v_currRecDepth_263_; lean_object* v_ref_264_; lean_object* v_currNamespace_265_; lean_object* v_openDecls_266_; lean_object* v_initHeartbeats_267_; lean_object* v_maxHeartbeats_268_; lean_object* v_quotContext_269_; lean_object* v_currMacroScope_270_; lean_object* v_cancelTk_x3f_271_; uint8_t v_suppressElabErrors_272_; lean_object* v_inheritedTraceOptions_273_; lean_object* v___y_274_; uint8_t v___y_280_; uint8_t v___x_302_; 
v___x_238_ = lean_st_ref_get(v_a_236_);
v_fileName_239_ = lean_ctor_get(v_a_235_, 0);
v_fileMap_240_ = lean_ctor_get(v_a_235_, 1);
v_options_241_ = lean_ctor_get(v_a_235_, 2);
v_currRecDepth_242_ = lean_ctor_get(v_a_235_, 3);
v_ref_243_ = lean_ctor_get(v_a_235_, 5);
v_currNamespace_244_ = lean_ctor_get(v_a_235_, 6);
v_openDecls_245_ = lean_ctor_get(v_a_235_, 7);
v_initHeartbeats_246_ = lean_ctor_get(v_a_235_, 8);
v_maxHeartbeats_247_ = lean_ctor_get(v_a_235_, 9);
v_quotContext_248_ = lean_ctor_get(v_a_235_, 10);
v_currMacroScope_249_ = lean_ctor_get(v_a_235_, 11);
v_cancelTk_x3f_250_ = lean_ctor_get(v_a_235_, 12);
v_suppressElabErrors_251_ = lean_ctor_get_uint8(v_a_235_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_252_ = lean_ctor_get(v_a_235_, 13);
v_env_253_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_env_253_);
lean_dec(v___x_238_);
v___x_254_ = lean_box(1);
v___x_255_ = l_Lean_pp_mvars_anonymous;
v___x_256_ = 0;
lean_inc_ref(v_options_241_);
v___x_257_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_241_, v___x_255_, v___x_256_);
v___x_258_ = l_Lean_diagnostics;
v___x_259_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_257_, v___x_258_);
v___x_302_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_253_);
lean_dec_ref(v_env_253_);
if (v___x_302_ == 0)
{
if (v___x_259_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 1;
v___y_280_ = v___x_303_;
goto v___jp_279_;
}
else
{
v___y_280_ = v___x_302_;
goto v___jp_279_;
}
}
else
{
v___y_280_ = v___x_259_;
goto v___jp_279_;
}
v___jp_260_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = l_Lean_maxRecDepth;
v___x_276_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_257_, v___x_275_);
lean_inc_ref(v_inheritedTraceOptions_273_);
lean_inc(v_cancelTk_x3f_271_);
lean_inc(v_currMacroScope_270_);
lean_inc(v_quotContext_269_);
lean_inc(v_maxHeartbeats_268_);
lean_inc(v_initHeartbeats_267_);
lean_inc(v_openDecls_266_);
lean_inc(v_currNamespace_265_);
lean_inc(v_ref_264_);
lean_inc(v_currRecDepth_263_);
lean_inc_ref(v_fileMap_262_);
lean_inc_ref(v_fileName_261_);
v___x_277_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_277_, 0, v_fileName_261_);
lean_ctor_set(v___x_277_, 1, v_fileMap_262_);
lean_ctor_set(v___x_277_, 2, v___x_257_);
lean_ctor_set(v___x_277_, 3, v_currRecDepth_263_);
lean_ctor_set(v___x_277_, 4, v___x_276_);
lean_ctor_set(v___x_277_, 5, v_ref_264_);
lean_ctor_set(v___x_277_, 6, v_currNamespace_265_);
lean_ctor_set(v___x_277_, 7, v_openDecls_266_);
lean_ctor_set(v___x_277_, 8, v_initHeartbeats_267_);
lean_ctor_set(v___x_277_, 9, v_maxHeartbeats_268_);
lean_ctor_set(v___x_277_, 10, v_quotContext_269_);
lean_ctor_set(v___x_277_, 11, v_currMacroScope_270_);
lean_ctor_set(v___x_277_, 12, v_cancelTk_x3f_271_);
lean_ctor_set(v___x_277_, 13, v_inheritedTraceOptions_273_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*14, v___x_259_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*14 + 1, v_suppressElabErrors_272_);
v___x_278_ = l_Lean_PrettyPrinter_delab(v_e_232_, v___x_254_, v_a_233_, v_a_234_, v___x_277_, v___y_274_);
lean_dec_ref_known(v___x_277_, 14);
return v___x_278_;
}
v___jp_279_:
{
uint8_t v___x_281_; 
v___x_281_ = lean_bool_not(v___y_280_);
if (v___x_281_ == 0)
{
v_fileName_261_ = v_fileName_239_;
v_fileMap_262_ = v_fileMap_240_;
v_currRecDepth_263_ = v_currRecDepth_242_;
v_ref_264_ = v_ref_243_;
v_currNamespace_265_ = v_currNamespace_244_;
v_openDecls_266_ = v_openDecls_245_;
v_initHeartbeats_267_ = v_initHeartbeats_246_;
v_maxHeartbeats_268_ = v_maxHeartbeats_247_;
v_quotContext_269_ = v_quotContext_248_;
v_currMacroScope_270_ = v_currMacroScope_249_;
v_cancelTk_x3f_271_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_272_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_273_ = v_inheritedTraceOptions_252_;
v___y_274_ = v_a_236_;
goto v___jp_260_;
}
else
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v_nextMacroScope_284_; lean_object* v_ngen_285_; lean_object* v_auxDeclNGen_286_; lean_object* v_traceState_287_; lean_object* v_messages_288_; lean_object* v_infoState_289_; lean_object* v_snapshotTasks_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v___x_282_ = lean_st_ref_take(v_a_236_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
v_nextMacroScope_284_ = lean_ctor_get(v___x_282_, 1);
v_ngen_285_ = lean_ctor_get(v___x_282_, 2);
v_auxDeclNGen_286_ = lean_ctor_get(v___x_282_, 3);
v_traceState_287_ = lean_ctor_get(v___x_282_, 4);
v_messages_288_ = lean_ctor_get(v___x_282_, 6);
v_infoState_289_ = lean_ctor_get(v___x_282_, 7);
v_snapshotTasks_290_ = lean_ctor_get(v___x_282_, 8);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_282_, 5);
lean_dec(v_unused_301_);
v___x_292_ = v___x_282_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_snapshotTasks_290_);
lean_inc(v_infoState_289_);
lean_inc(v_messages_288_);
lean_inc(v_traceState_287_);
lean_inc(v_auxDeclNGen_286_);
lean_inc(v_ngen_285_);
lean_inc(v_nextMacroScope_284_);
lean_inc(v_env_283_);
lean_dec(v___x_282_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_294_ = l_Lean_Kernel_enableDiag(v_env_283_, v___x_259_);
v___x_295_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 5, v___x_295_);
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_nextMacroScope_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_ngen_285_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_auxDeclNGen_286_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_traceState_287_);
lean_ctor_set(v_reuseFailAlloc_299_, 5, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_299_, 6, v_messages_288_);
lean_ctor_set(v_reuseFailAlloc_299_, 7, v_infoState_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 8, v_snapshotTasks_290_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_st_ref_set(v_a_236_, v___x_297_);
v_fileName_261_ = v_fileName_239_;
v_fileMap_262_ = v_fileMap_240_;
v_currRecDepth_263_ = v_currRecDepth_242_;
v_ref_264_ = v_ref_243_;
v_currNamespace_265_ = v_currNamespace_244_;
v_openDecls_266_ = v_openDecls_245_;
v_initHeartbeats_267_ = v_initHeartbeats_246_;
v_maxHeartbeats_268_ = v_maxHeartbeats_247_;
v_quotContext_269_ = v_quotContext_248_;
v_currMacroScope_270_ = v_currMacroScope_249_;
v_cancelTk_x3f_271_ = v_cancelTk_x3f_250_;
v_suppressElabErrors_272_ = v_suppressElabErrors_251_;
v_inheritedTraceOptions_273_ = v_inheritedTraceOptions_252_;
v___y_274_ = v_a_236_;
goto v___jp_260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___boxed(lean_object* v_e_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v_mctx_320_; lean_object* v_lctx_321_; lean_object* v_options_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_317_ = lean_st_ref_get(v___y_315_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = lean_st_ref_get(v___y_313_);
v_mctx_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_mctx_320_);
lean_dec(v___x_319_);
v_lctx_321_ = lean_ctor_get(v___y_312_, 2);
v_options_322_ = lean_ctor_get(v___y_314_, 2);
lean_inc_ref(v_options_322_);
lean_inc_ref(v_lctx_321_);
v___x_323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_323_, 0, v_env_318_);
lean_ctor_set(v___x_323_, 1, v_mctx_320_);
lean_ctor_set(v___x_323_, 2, v_lctx_321_);
lean_ctor_set(v___x_323_, 3, v_options_322_);
v___x_324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_msgData_311_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0___boxed(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msgData_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; 
lean_inc_ref(v_e_336_);
v___x_342_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_358_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_MessageData_ofExpr(v_e_336_);
v___x_345_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_344_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_358_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_350_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1));
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_a_343_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_a_346_);
v___x_354_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_354_, 0, v___x_351_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
lean_ctor_set(v___x_354_, 2, v___x_352_);
lean_ctor_set(v___x_354_, 3, v___x_352_);
lean_ctor_set(v___x_354_, 4, v___x_353_);
lean_ctor_set(v___x_354_, 5, v___x_352_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_354_);
v___x_356_ = v___x_348_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_e_336_);
v_a_359_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_342_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_342_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___boxed(lean_object* v_e_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
return v_res_373_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_374_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
lean_ctor_set(v___x_379_, 3, v___x_378_);
lean_ctor_set(v___x_379_, 4, v___x_377_);
lean_ctor_set(v___x_379_, 5, v___x_377_);
lean_ctor_set(v___x_379_, 6, v___x_377_);
lean_ctor_set(v___x_379_, 7, v___x_377_);
lean_ctor_set(v___x_379_, 8, v___x_377_);
lean_ctor_set(v___x_379_, 9, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_unsigned_to_nat(32u);
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_383_ = ((size_t)5ULL);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_unsigned_to_nat(32u);
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3);
v___x_388_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_384_);
lean_ctor_set(v___x_388_, 3, v___x_384_);
lean_ctor_set_usize(v___x_388_, 4, v___x_383_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = lean_box(1);
v___x_390_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4);
v___x_391_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
v___x_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
lean_ctor_set(v___x_392_, 2, v___x_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(lean_object* v_msgData_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_env_398_; lean_object* v_options_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_397_ = lean_st_ref_get(v___y_395_);
v_env_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_env_398_);
lean_dec(v___x_397_);
v_options_399_ = lean_ctor_get(v___y_394_, 2);
v___x_400_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2);
v___x_401_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_399_);
v___x_402_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_402_, 0, v_env_398_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_401_);
lean_ctor_set(v___x_402_, 3, v_options_399_);
v___x_403_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_msgData_393_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msgData_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(uint8_t v___y_416_, uint8_t v_suppressElabErrors_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 1)
{
lean_object* v_pre_419_; 
v_pre_419_ = lean_ctor_get(v_x_418_, 0);
switch(lean_obj_tag(v_pre_419_))
{
case 1:
{
lean_object* v_pre_420_; 
v_pre_420_ = lean_ctor_get(v_pre_419_, 0);
switch(lean_obj_tag(v_pre_420_))
{
case 0:
{
lean_object* v_str_421_; lean_object* v_str_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_str_421_ = lean_ctor_get(v_x_418_, 1);
v_str_422_ = lean_ctor_get(v_pre_419_, 1);
v___x_423_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0));
v___x_424_ = lean_string_dec_eq(v_str_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4));
v___x_426_ = lean_string_dec_eq(v_str_422_, v___x_425_);
if (v___x_426_ == 0)
{
return v___y_416_;
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1));
v___x_428_ = lean_string_dec_eq(v_str_421_, v___x_427_);
if (v___x_428_ == 0)
{
return v___y_416_;
}
else
{
return v_suppressElabErrors_417_;
}
}
}
else
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2));
v___x_430_ = lean_string_dec_eq(v_str_421_, v___x_429_);
if (v___x_430_ == 0)
{
return v___y_416_;
}
else
{
return v_suppressElabErrors_417_;
}
}
}
case 1:
{
lean_object* v_pre_431_; 
v_pre_431_ = lean_ctor_get(v_pre_420_, 0);
if (lean_obj_tag(v_pre_431_) == 0)
{
lean_object* v_str_432_; lean_object* v_str_433_; lean_object* v_str_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_str_432_ = lean_ctor_get(v_x_418_, 1);
v_str_433_ = lean_ctor_get(v_pre_419_, 1);
v_str_434_ = lean_ctor_get(v_pre_420_, 1);
v___x_435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3));
v___x_436_ = lean_string_dec_eq(v_str_434_, v___x_435_);
if (v___x_436_ == 0)
{
return v___y_416_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4));
v___x_438_ = lean_string_dec_eq(v_str_433_, v___x_437_);
if (v___x_438_ == 0)
{
return v___y_416_;
}
else
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5));
v___x_440_ = lean_string_dec_eq(v_str_432_, v___x_439_);
if (v___x_440_ == 0)
{
return v___y_416_;
}
else
{
return v_suppressElabErrors_417_;
}
}
}
}
else
{
return v___y_416_;
}
}
default: 
{
return v___y_416_;
}
}
}
case 0:
{
lean_object* v_str_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_str_441_ = lean_ctor_get(v_x_418_, 1);
v___x_442_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0));
v___x_443_ = lean_string_dec_eq(v_str_441_, v___x_442_);
if (v___x_443_ == 0)
{
return v___y_416_;
}
else
{
return v_suppressElabErrors_417_;
}
}
default: 
{
return v___y_416_;
}
}
}
else
{
return v___y_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(lean_object* v___y_444_, lean_object* v_suppressElabErrors_445_, lean_object* v_x_446_){
_start:
{
uint8_t v___y_2411__boxed_447_; uint8_t v_suppressElabErrors_boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v___y_2411__boxed_447_ = lean_unbox(v___y_444_);
v_suppressElabErrors_boxed_448_ = lean_unbox(v_suppressElabErrors_445_);
v_res_449_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v___y_2411__boxed_447_, v_suppressElabErrors_boxed_448_, v_x_446_);
lean_dec(v_x_446_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(lean_object* v_ref_452_, lean_object* v_msgData_453_, uint8_t v_severity_454_, uint8_t v_isSilent_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_496_; uint8_t v___y_497_; lean_object* v___y_498_; uint8_t v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_523_; uint8_t v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; lean_object* v___y_532_; uint8_t v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_538_; uint8_t v___x_543_; lean_object* v___y_545_; uint8_t v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; uint8_t v___y_551_; uint8_t v___y_553_; uint8_t v___x_568_; 
v___x_543_ = 2;
v___x_568_ = l_Lean_instBEqMessageSeverity_beq(v_severity_454_, v___x_543_);
if (v___x_568_ == 0)
{
v___y_553_ = v___x_568_;
goto v___jp_552_;
}
else
{
uint8_t v___x_569_; 
lean_inc_ref(v_msgData_453_);
v___x_569_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_453_);
v___y_553_ = v___x_569_;
goto v___jp_552_;
}
v___jp_459_:
{
lean_object* v___x_469_; lean_object* v_currNamespace_470_; lean_object* v_openDecls_471_; lean_object* v_env_472_; lean_object* v_nextMacroScope_473_; lean_object* v_ngen_474_; lean_object* v_auxDeclNGen_475_; lean_object* v_traceState_476_; lean_object* v_cache_477_; lean_object* v_messages_478_; lean_object* v_infoState_479_; lean_object* v_snapshotTasks_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_494_; 
v___x_469_ = lean_st_ref_take(v___y_468_);
v_currNamespace_470_ = lean_ctor_get(v___y_467_, 6);
v_openDecls_471_ = lean_ctor_get(v___y_467_, 7);
v_env_472_ = lean_ctor_get(v___x_469_, 0);
v_nextMacroScope_473_ = lean_ctor_get(v___x_469_, 1);
v_ngen_474_ = lean_ctor_get(v___x_469_, 2);
v_auxDeclNGen_475_ = lean_ctor_get(v___x_469_, 3);
v_traceState_476_ = lean_ctor_get(v___x_469_, 4);
v_cache_477_ = lean_ctor_get(v___x_469_, 5);
v_messages_478_ = lean_ctor_get(v___x_469_, 6);
v_infoState_479_ = lean_ctor_get(v___x_469_, 7);
v_snapshotTasks_480_ = lean_ctor_get(v___x_469_, 8);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_494_ == 0)
{
v___x_482_ = v___x_469_;
v_isShared_483_ = v_isSharedCheck_494_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snapshotTasks_480_);
lean_inc(v_infoState_479_);
lean_inc(v_messages_478_);
lean_inc(v_cache_477_);
lean_inc(v_traceState_476_);
lean_inc(v_auxDeclNGen_475_);
lean_inc(v_ngen_474_);
lean_inc(v_nextMacroScope_473_);
lean_inc(v_env_472_);
lean_dec(v___x_469_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_494_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
lean_inc(v_openDecls_471_);
lean_inc(v_currNamespace_470_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_currNamespace_470_);
lean_ctor_set(v___x_484_, 1, v_openDecls_471_);
v___x_485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___y_465_);
lean_inc_ref(v___y_462_);
lean_inc_ref(v___y_460_);
v___x_486_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_486_, 0, v___y_460_);
lean_ctor_set(v___x_486_, 1, v___y_463_);
lean_ctor_set(v___x_486_, 2, v___y_464_);
lean_ctor_set(v___x_486_, 3, v___y_462_);
lean_ctor_set(v___x_486_, 4, v___x_485_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5, v___y_461_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5 + 1, v___y_466_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5 + 2, v_isSilent_455_);
v___x_487_ = l_Lean_MessageLog_add(v___x_486_, v_messages_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 6, v___x_487_);
v___x_489_ = v___x_482_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_env_472_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_nextMacroScope_473_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_ngen_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_auxDeclNGen_475_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_traceState_476_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_cache_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_infoState_479_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_snapshotTasks_480_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_st_ref_set(v___y_468_, v___x_489_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
v___jp_495_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_519_; 
v___x_504_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_453_);
v___x_505_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v___x_504_, v___y_456_, v___y_457_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_519_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc_ref_n(v___y_500_, 2);
v___x_510_ = l_Lean_FileMap_toPosition(v___y_500_, v___y_501_);
lean_dec(v___y_501_);
v___x_511_ = l_Lean_FileMap_toPosition(v___y_500_, v___y_503_);
lean_dec(v___y_503_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
v___x_513_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_497_ == 0)
{
lean_del_object(v___x_508_);
lean_dec_ref(v___y_496_);
v___y_460_ = v___y_498_;
v___y_461_ = v___y_499_;
v___y_462_ = v___x_513_;
v___y_463_ = v___x_510_;
v___y_464_ = v___x_512_;
v___y_465_ = v_a_506_;
v___y_466_ = v___y_502_;
v___y_467_ = v___y_456_;
v___y_468_ = v___y_457_;
goto v___jp_459_;
}
else
{
uint8_t v___x_514_; 
lean_inc(v_a_506_);
v___x_514_ = l_Lean_MessageData_hasTag(v___y_496_, v_a_506_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec_ref_known(v___x_512_, 1);
lean_dec_ref(v___x_510_);
lean_dec(v_a_506_);
v___x_515_ = lean_box(0);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_515_);
v___x_517_ = v___x_508_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
else
{
lean_del_object(v___x_508_);
v___y_460_ = v___y_498_;
v___y_461_ = v___y_499_;
v___y_462_ = v___x_513_;
v___y_463_ = v___x_510_;
v___y_464_ = v___x_512_;
v___y_465_ = v_a_506_;
v___y_466_ = v___y_502_;
v___y_467_ = v___y_456_;
v___y_468_ = v___y_457_;
goto v___jp_459_;
}
}
}
}
v___jp_520_:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Syntax_getTailPos_x3f(v___y_526_, v___y_524_);
lean_dec(v___y_526_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_inc(v___y_528_);
v___y_496_ = v___y_521_;
v___y_497_ = v___y_522_;
v___y_498_ = v___y_523_;
v___y_499_ = v___y_524_;
v___y_500_ = v___y_525_;
v___y_501_ = v___y_528_;
v___y_502_ = v___y_527_;
v___y_503_ = v___y_528_;
goto v___jp_495_;
}
else
{
lean_object* v_val_530_; 
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_529_, 1);
v___y_496_ = v___y_521_;
v___y_497_ = v___y_522_;
v___y_498_ = v___y_523_;
v___y_499_ = v___y_524_;
v___y_500_ = v___y_525_;
v___y_501_ = v___y_528_;
v___y_502_ = v___y_527_;
v___y_503_ = v_val_530_;
goto v___jp_495_;
}
}
v___jp_531_:
{
lean_object* v_ref_539_; lean_object* v___x_540_; 
v_ref_539_ = l_Lean_replaceRef(v_ref_452_, v___y_537_);
v___x_540_ = l_Lean_Syntax_getPos_x3f(v_ref_539_, v___y_535_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___y_521_ = v___y_532_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_534_;
v___y_524_ = v___y_535_;
v___y_525_ = v___y_536_;
v___y_526_ = v_ref_539_;
v___y_527_ = v___y_538_;
v___y_528_ = v___x_541_;
goto v___jp_520_;
}
else
{
lean_object* v_val_542_; 
v_val_542_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_540_, 1);
v___y_521_ = v___y_532_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_534_;
v___y_524_ = v___y_535_;
v___y_525_ = v___y_536_;
v___y_526_ = v_ref_539_;
v___y_527_ = v___y_538_;
v___y_528_ = v_val_542_;
goto v___jp_520_;
}
}
v___jp_544_:
{
if (v___y_551_ == 0)
{
v___y_532_ = v___y_545_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_547_;
v___y_535_ = v___y_550_;
v___y_536_ = v___y_548_;
v___y_537_ = v___y_549_;
v___y_538_ = v_severity_454_;
goto v___jp_531_;
}
else
{
v___y_532_ = v___y_545_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_547_;
v___y_535_ = v___y_550_;
v___y_536_ = v___y_548_;
v___y_537_ = v___y_549_;
v___y_538_ = v___x_543_;
goto v___jp_531_;
}
}
v___jp_552_:
{
if (v___y_553_ == 0)
{
lean_object* v_fileName_554_; lean_object* v_fileMap_555_; lean_object* v_options_556_; lean_object* v_ref_557_; uint8_t v_suppressElabErrors_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___f_561_; uint8_t v___x_562_; uint8_t v___x_563_; 
v_fileName_554_ = lean_ctor_get(v___y_456_, 0);
v_fileMap_555_ = lean_ctor_get(v___y_456_, 1);
v_options_556_ = lean_ctor_get(v___y_456_, 2);
v_ref_557_ = lean_ctor_get(v___y_456_, 5);
v_suppressElabErrors_558_ = lean_ctor_get_uint8(v___y_456_, sizeof(void*)*14 + 1);
v___x_559_ = lean_box(v___y_553_);
v___x_560_ = lean_box(v_suppressElabErrors_558_);
v___f_561_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_561_, 0, v___x_559_);
lean_closure_set(v___f_561_, 1, v___x_560_);
v___x_562_ = 1;
v___x_563_ = l_Lean_instBEqMessageSeverity_beq(v_severity_454_, v___x_562_);
if (v___x_563_ == 0)
{
v___y_545_ = v___f_561_;
v___y_546_ = v_suppressElabErrors_558_;
v___y_547_ = v_fileName_554_;
v___y_548_ = v_fileMap_555_;
v___y_549_ = v_ref_557_;
v___y_550_ = v___y_553_;
v___y_551_ = v___x_563_;
goto v___jp_544_;
}
else
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = l_Lean_warningAsError;
v___x_565_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_556_, v___x_564_);
v___y_545_ = v___f_561_;
v___y_546_ = v_suppressElabErrors_558_;
v___y_547_ = v_fileName_554_;
v___y_548_ = v_fileMap_555_;
v___y_549_ = v_ref_557_;
v___y_550_ = v___y_553_;
v___y_551_ = v___x_565_;
goto v___jp_544_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v_msgData_453_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___boxed(lean_object* v_ref_570_, lean_object* v_msgData_571_, lean_object* v_severity_572_, lean_object* v_isSilent_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_severity_boxed_577_; uint8_t v_isSilent_boxed_578_; lean_object* v_res_579_; 
v_severity_boxed_577_ = lean_unbox(v_severity_572_);
v_isSilent_boxed_578_ = lean_unbox(v_isSilent_573_);
v_res_579_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_570_, v_msgData_571_, v_severity_boxed_577_, v_isSilent_boxed_578_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v_ref_570_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object* v_ref_580_, lean_object* v_msgData_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = 0;
v___x_586_ = 0;
v___x_587_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_580_, v_msgData_581_, v___x_585_, v___x_586_, v___y_582_, v___y_583_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object* v_ref_588_, lean_object* v_msgData_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_588_, v_msgData_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v_ref_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* v_ref_594_, lean_object* v_s_595_, lean_object* v_origSpan_x3f_596_, lean_object* v_header_597_, lean_object* v_codeActionPrefix_x3f_598_, uint8_t v_diffGranularity_599_, lean_object* v_footer_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_hintSuggestion_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; 
v___x_604_ = lean_box(0);
v_hintSuggestion_605_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_hintSuggestion_605_, 0, v_s_595_);
lean_ctor_set(v_hintSuggestion_605_, 1, v_origSpan_x3f_596_);
lean_ctor_set(v_hintSuggestion_605_, 2, v___x_604_);
lean_ctor_set_uint8(v_hintSuggestion_605_, sizeof(void*)*3, v_diffGranularity_599_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_array_push(v___x_607_, v_hintSuggestion_605_);
v___x_609_ = 0;
lean_inc(v_ref_594_);
v___x_610_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v___x_608_, v_ref_594_, v_codeActionPrefix_x3f_598_, v___x_609_, v_a_601_, v_a_602_);
lean_dec_ref(v___x_608_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_stringToMessageData(v_header_597_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_a_611_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_footer_600_);
v___x_615_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_594_, v___x_614_, v_a_601_, v_a_602_);
lean_dec(v_ref_594_);
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_footer_600_);
lean_dec_ref(v_header_597_);
lean_dec(v_ref_594_);
v_a_616_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_610_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_610_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* v_ref_624_, lean_object* v_s_625_, lean_object* v_origSpan_x3f_626_, lean_object* v_header_627_, lean_object* v_codeActionPrefix_x3f_628_, lean_object* v_diffGranularity_629_, lean_object* v_footer_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
uint8_t v_diffGranularity_boxed_634_; lean_object* v_res_635_; 
v_diffGranularity_boxed_634_ = lean_unbox(v_diffGranularity_629_);
v_res_635_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_624_, v_s_625_, v_origSpan_x3f_626_, v_header_627_, v_codeActionPrefix_x3f_628_, v_diffGranularity_boxed_634_, v_footer_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_ref_640_; lean_object* v___x_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_ref_640_ = lean_ctor_get(v___y_637_, 5);
v___x_641_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msg_636_, v___y_637_, v___y_638_);
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_650_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
lean_inc(v_ref_640_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_ref_640_);
lean_ctor_set(v___x_646_, 1, v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
lean_ctor_set(v___x_644_, 0, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(lean_object* v_ref_656_, lean_object* v_msg_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_fileName_661_; lean_object* v_fileMap_662_; lean_object* v_options_663_; lean_object* v_currRecDepth_664_; lean_object* v_maxRecDepth_665_; lean_object* v_ref_666_; lean_object* v_currNamespace_667_; lean_object* v_openDecls_668_; lean_object* v_initHeartbeats_669_; lean_object* v_maxHeartbeats_670_; lean_object* v_quotContext_671_; lean_object* v_currMacroScope_672_; uint8_t v_diag_673_; lean_object* v_cancelTk_x3f_674_; uint8_t v_suppressElabErrors_675_; lean_object* v_inheritedTraceOptions_676_; lean_object* v_ref_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_fileName_661_ = lean_ctor_get(v___y_658_, 0);
v_fileMap_662_ = lean_ctor_get(v___y_658_, 1);
v_options_663_ = lean_ctor_get(v___y_658_, 2);
v_currRecDepth_664_ = lean_ctor_get(v___y_658_, 3);
v_maxRecDepth_665_ = lean_ctor_get(v___y_658_, 4);
v_ref_666_ = lean_ctor_get(v___y_658_, 5);
v_currNamespace_667_ = lean_ctor_get(v___y_658_, 6);
v_openDecls_668_ = lean_ctor_get(v___y_658_, 7);
v_initHeartbeats_669_ = lean_ctor_get(v___y_658_, 8);
v_maxHeartbeats_670_ = lean_ctor_get(v___y_658_, 9);
v_quotContext_671_ = lean_ctor_get(v___y_658_, 10);
v_currMacroScope_672_ = lean_ctor_get(v___y_658_, 11);
v_diag_673_ = lean_ctor_get_uint8(v___y_658_, sizeof(void*)*14);
v_cancelTk_x3f_674_ = lean_ctor_get(v___y_658_, 12);
v_suppressElabErrors_675_ = lean_ctor_get_uint8(v___y_658_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_676_ = lean_ctor_get(v___y_658_, 13);
v_ref_677_ = l_Lean_replaceRef(v_ref_656_, v_ref_666_);
lean_inc_ref(v_inheritedTraceOptions_676_);
lean_inc(v_cancelTk_x3f_674_);
lean_inc(v_currMacroScope_672_);
lean_inc(v_quotContext_671_);
lean_inc(v_maxHeartbeats_670_);
lean_inc(v_initHeartbeats_669_);
lean_inc(v_openDecls_668_);
lean_inc(v_currNamespace_667_);
lean_inc(v_maxRecDepth_665_);
lean_inc(v_currRecDepth_664_);
lean_inc_ref(v_options_663_);
lean_inc_ref(v_fileMap_662_);
lean_inc_ref(v_fileName_661_);
v___x_678_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_678_, 0, v_fileName_661_);
lean_ctor_set(v___x_678_, 1, v_fileMap_662_);
lean_ctor_set(v___x_678_, 2, v_options_663_);
lean_ctor_set(v___x_678_, 3, v_currRecDepth_664_);
lean_ctor_set(v___x_678_, 4, v_maxRecDepth_665_);
lean_ctor_set(v___x_678_, 5, v_ref_677_);
lean_ctor_set(v___x_678_, 6, v_currNamespace_667_);
lean_ctor_set(v___x_678_, 7, v_openDecls_668_);
lean_ctor_set(v___x_678_, 8, v_initHeartbeats_669_);
lean_ctor_set(v___x_678_, 9, v_maxHeartbeats_670_);
lean_ctor_set(v___x_678_, 10, v_quotContext_671_);
lean_ctor_set(v___x_678_, 11, v_currMacroScope_672_);
lean_ctor_set(v___x_678_, 12, v_cancelTk_x3f_674_);
lean_ctor_set(v___x_678_, 13, v_inheritedTraceOptions_676_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*14, v_diag_673_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*14 + 1, v_suppressElabErrors_675_);
v___x_679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_657_, v___x_678_, v___y_659_);
lean_dec_ref_known(v___x_678_, 14);
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
uint8_t v___x_862_; uint8_t v___x_863_; 
v___x_862_ = l_Lean_Expr_hasMVar(v_e_859_);
v___x_863_ = lean_bool_not(v___x_862_);
if (v___x_863_ == 0)
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
v___x_879_ = lean_st_ref_set(v___y_860_, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_fst_867_);
return v___x_880_;
}
}
}
else
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_e_859_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(lean_object* v_e_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_885_, v___y_886_);
lean_dec(v___y_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(lean_object* v_e_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_889_, v___y_895_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(lean_object* v_e_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(lean_object* v_msg_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_ref_917_; lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_ref_917_ = lean_ctor_get(v___y_914_, 5);
v___x_918_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msg_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_927_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_inc(v_ref_917_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_ref_917_);
lean_ctor_set(v___x_923_, 1, v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 1);
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_934_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* v_initialState_938_, lean_object* v_tac_939_, lean_object* v_expectedType_x3f_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_942_, v_a_944_, v_a_946_, v_a_948_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; lean_object* v_a_954_; lean_object* v_a_965_; lean_object* v___y_976_; lean_object* v___x_979_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = 0;
v___x_979_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_initialState_938_, v___x_952_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref_known(v___x_979_, 1);
v___x_980_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_980_, 0, v_tac_939_);
v___x_981_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_981_, 0, lean_box(0));
lean_closure_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v___x_981_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref_known(v___x_982_, 1);
if (lean_obj_tag(v_expectedType_x3f_940_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_984_; 
v_val_983_ = lean_ctor_get(v_expectedType_x3f_940_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_expectedType_x3f_940_, 1);
v___x_984_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_942_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lean_MVarId_getType(v_a_985_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v_a_991_; uint8_t v___x_992_; uint8_t v___x_993_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_987_, v_a_946_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref(v___x_988_);
v___x_990_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_val_983_, v_a_946_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref(v___x_990_);
v___x_992_ = lean_expr_eqv(v_a_989_, v_a_991_);
lean_dec(v_a_991_);
lean_dec(v_a_989_);
v___x_993_ = lean_bool_not(v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_box(0);
v_a_965_ = v___x_994_;
goto v___jp_964_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
v___x_996_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v___x_995_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
v___y_976_ = v___x_996_;
goto v___jp_975_;
}
}
else
{
lean_object* v_a_997_; 
lean_dec(v_val_983_);
v_a_997_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_986_, 1);
v_a_954_ = v_a_997_;
goto v___jp_953_;
}
}
else
{
lean_object* v_a_998_; 
lean_dec(v_val_983_);
v_a_998_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_984_, 1);
v_a_954_ = v_a_998_;
goto v___jp_953_;
}
}
else
{
lean_object* v___x_999_; 
lean_dec(v_expectedType_x3f_940_);
v___x_999_ = lean_box(0);
v_a_965_ = v___x_999_;
goto v___jp_964_;
}
}
else
{
lean_dec(v_expectedType_x3f_940_);
v___y_976_ = v___x_982_;
goto v___jp_975_;
}
}
else
{
lean_dec(v_a_951_);
lean_dec(v_expectedType_x3f_940_);
lean_dec(v_tac_939_);
return v___x_979_;
}
v___jp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_951_, v___x_952_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_963_);
v___x_957_ = v___x_955_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_dec(v___x_955_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 1);
lean_ctor_set(v___x_957_, 0, v_a_954_);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_954_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_dec_ref(v_a_954_);
return v___x_955_;
}
}
v___jp_964_:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_951_, v___x_952_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_966_, 0);
lean_dec(v_unused_974_);
v___x_968_ = v___x_966_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_dec(v___x_966_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_a_965_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_965_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
return v___x_966_;
}
}
v___jp_975_:
{
if (lean_obj_tag(v___y_976_) == 0)
{
lean_object* v_a_977_; 
v_a_977_ = lean_ctor_get(v___y_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___y_976_, 1);
v_a_965_ = v_a_977_;
goto v___jp_964_;
}
else
{
lean_object* v_a_978_; 
v_a_978_ = lean_ctor_get(v___y_976_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___y_976_, 1);
v_a_954_ = v_a_978_;
goto v___jp_953_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_expectedType_x3f_940_);
lean_dec(v_tac_939_);
lean_dec_ref(v_initialState_938_);
v_a_1000_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_950_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_950_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object* v_initialState_1008_, lean_object* v_tac_1009_, lean_object* v_expectedType_x3f_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1008_, v_tac_1009_, v_expectedType_x3f_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(lean_object* v_00_u03b1_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_1022_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(v_00_u03b1_1033_, v_msg_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* v_tac_1082_, lean_object* v_msg_1083_, lean_object* v_initialState_1084_, lean_object* v_expectedType_x3f_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1087_, v_a_1089_, v_a_1091_, v_a_1093_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
lean_inc(v_expectedType_x3f_1085_);
lean_inc(v_tac_1082_);
lean_inc_ref(v_initialState_1084_);
v___x_1120_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1084_, v_tac_1082_, v_expectedType_x3f_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_a_1119_);
lean_dec(v_expectedType_x3f_1085_);
lean_dec_ref(v_initialState_1084_);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1120_, 0);
lean_dec(v_unused_1130_);
v___x_1122_ = v___x_1120_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v___x_1120_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_tac_1082_);
lean_ctor_set(v___x_1124_, 1, v_msg_1083_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1199_; 
v_a_1131_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1133_ = v___x_1120_;
v_isShared_1134_ = v_isSharedCheck_1199_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1120_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1199_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___y_1136_; uint8_t v___x_1197_; 
v___x_1197_ = l_Lean_Exception_isInterrupt(v_a_1131_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
lean_inc(v_a_1131_);
v___x_1198_ = l_Lean_Exception_isRuntime(v_a_1131_);
v___y_1136_ = v___x_1198_;
goto v___jp_1135_;
}
else
{
v___y_1136_ = v___x_1197_;
goto v___jp_1135_;
}
v___jp_1135_:
{
if (v___y_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_del_object(v___x_1133_);
lean_dec(v_a_1131_);
v___x_1137_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1119_, v___y_1136_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_ref_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref_known(v___x_1137_, 1);
v_ref_1138_ = lean_ctor_get(v_a_1092_, 5);
v___x_1139_ = l_Lean_SourceInfo_fromRef(v_ref_1138_, v___y_1136_);
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2));
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3));
lean_inc_n(v___x_1139_, 6);
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5));
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7));
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11));
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12));
v___x_1148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1139_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_Syntax_node1(v___x_1139_, v___x_1146_, v___x_1148_);
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13));
v___x_1151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1139_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_Syntax_node3(v___x_1139_, v___x_1145_, v___x_1149_, v___x_1151_, v_tac_1082_);
v___x_1153_ = l_Lean_Syntax_node1(v___x_1139_, v___x_1144_, v___x_1152_);
v___x_1154_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1087_, v_a_1089_, v_a_1091_, v_a_1093_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
lean_inc_n(v___x_1139_, 2);
v___x_1156_ = l_Lean_Syntax_node1(v___x_1139_, v___x_1143_, v___x_1153_);
v___x_1157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1139_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_Syntax_node3(v___x_1139_, v___x_1140_, v___x_1142_, v___x_1156_, v___x_1158_);
lean_inc(v___x_1159_);
v___x_1160_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1084_, v___x_1159_, v_expectedType_x3f_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_a_1155_);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v___x_1160_, 0);
lean_dec(v_unused_1174_);
v___x_1162_ = v___x_1160_;
v_isShared_1163_ = v_isSharedCheck_1173_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v___x_1160_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1173_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_msg_1083_);
v___x_1166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1159_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1169_);
v___x_1171_ = v___x_1162_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1175_; uint8_t v___x_1176_; 
lean_dec(v___x_1159_);
lean_dec_ref(v_msg_1083_);
v_a_1175_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1176_ = l_Lean_Exception_isInterrupt(v_a_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
lean_inc(v_a_1175_);
v___x_1177_ = l_Lean_Exception_isRuntime(v_a_1175_);
v___y_1096_ = v_a_1175_;
v___y_1097_ = v_a_1155_;
v___y_1098_ = v___x_1177_;
goto v___jp_1095_;
}
else
{
v___y_1096_ = v_a_1175_;
v___y_1097_ = v_a_1155_;
v___y_1098_ = v___x_1176_;
goto v___jp_1095_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v___x_1153_);
lean_dec_ref_known(v___x_1142_, 2);
lean_dec(v___x_1139_);
lean_dec(v_expectedType_x3f_1085_);
lean_dec_ref(v_initialState_1084_);
lean_dec_ref(v_msg_1083_);
v_a_1178_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1154_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1154_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_expectedType_x3f_1085_);
lean_dec_ref(v_initialState_1084_);
lean_dec_ref(v_msg_1083_);
lean_dec(v_tac_1082_);
v_a_1186_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1137_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1137_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1195_; 
lean_dec(v_a_1119_);
lean_dec(v_expectedType_x3f_1085_);
lean_dec_ref(v_initialState_1084_);
lean_dec_ref(v_msg_1083_);
lean_dec(v_tac_1082_);
if (v_isShared_1134_ == 0)
{
v___x_1195_ = v___x_1133_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1131_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_expectedType_x3f_1085_);
lean_dec_ref(v_initialState_1084_);
lean_dec_ref(v_msg_1083_);
lean_dec(v_tac_1082_);
v_a_1200_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1118_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1118_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
v___jp_1095_:
{
if (v___y_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v___y_1096_);
v___x_1099_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_1097_, v___y_1098_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___x_1099_, 0);
lean_dec(v_unused_1108_);
v___x_1101_ = v___x_1099_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v___x_1099_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1099_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1099_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec_ref(v___y_1097_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___y_1096_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object* v_tac_1208_, lean_object* v_msg_1209_, lean_object* v_initialState_1210_, lean_object* v_expectedType_x3f_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_tac_1208_, v_msg_1209_, v_initialState_1210_, v_expectedType_x3f_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
return v_res_1221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* v_targetKind_1231_, lean_object* v_invalidTactic_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_targetKind_1231_);
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = l_Lean_indentD(v_invalidTactic_1232_);
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0));
v___x_1243_ = l_Lean_stringToMessageData(v___x_1242_);
return v___x_1243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object* v_e_1259_, uint8_t v_useRefine_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___x_1271_; 
lean_inc_ref(v_e_1259_);
v___x_1271_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_1259_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_tac_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
if (v_useRefine_1260_ == 0)
{
lean_object* v_ref_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_ref_1287_ = lean_ctor_get(v___y_1263_, 5);
v___x_1288_ = l_Lean_SourceInfo_fromRef(v_ref_1287_, v_useRefine_1260_);
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4));
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5));
lean_inc(v___x_1288_);
v___x_1291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1288_);
lean_ctor_set(v___x_1291_, 1, v___x_1289_);
v___x_1292_ = l_Lean_Syntax_node2(v___x_1288_, v___x_1290_, v___x_1291_, v_a_1272_);
v_tac_1274_ = v___x_1292_;
v___y_1275_ = v___y_1261_;
v___y_1276_ = v___y_1262_;
v___y_1277_ = v___y_1263_;
v___y_1278_ = v___y_1264_;
goto v___jp_1273_;
}
else
{
lean_object* v_ref_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_ref_1293_ = lean_ctor_get(v___y_1263_, 5);
v___x_1294_ = 0;
v___x_1295_ = l_Lean_SourceInfo_fromRef(v_ref_1293_, v___x_1294_);
v___x_1296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6));
v___x_1297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7));
lean_inc(v___x_1295_);
v___x_1298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1295_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
v___x_1299_ = l_Lean_Syntax_node2(v___x_1295_, v___x_1297_, v___x_1298_, v_a_1272_);
v_tac_1274_ = v___x_1299_;
v___y_1275_ = v___y_1261_;
v___y_1276_ = v___y_1262_;
v___y_1277_ = v___y_1263_;
v___y_1278_ = v___y_1264_;
goto v___jp_1273_;
}
v___jp_1273_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = l_Lean_MessageData_ofExpr(v_e_1259_);
v___x_1280_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1279_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (v_useRefine_1260_ == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v_a_1281_);
v___y_1267_ = v_tac_1274_;
v___y_1268_ = v___x_1283_;
goto v___jp_1266_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1280_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v_a_1284_);
v___y_1267_ = v_tac_1274_;
v___y_1268_ = v___x_1286_;
goto v___jp_1266_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_e_1259_);
v_a_1300_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1271_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1271_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
v___jp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___y_1267_);
lean_ctor_set(v___x_1269_, 1, v___y_1268_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object* v_e_1308_, lean_object* v_useRefine_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_useRefine_boxed_1315_; lean_object* v_res_1316_; 
v_useRefine_boxed_1315_ = lean_unbox(v_useRefine_1309_);
v_res_1316_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_1308_, v_useRefine_boxed_1315_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* v_e_1317_, uint8_t v_useRefine_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v_fileName_1325_; lean_object* v_fileMap_1326_; lean_object* v_options_1327_; lean_object* v_currRecDepth_1328_; lean_object* v_ref_1329_; lean_object* v_currNamespace_1330_; lean_object* v_openDecls_1331_; lean_object* v_initHeartbeats_1332_; lean_object* v_maxHeartbeats_1333_; lean_object* v_quotContext_1334_; lean_object* v_currMacroScope_1335_; lean_object* v_cancelTk_x3f_1336_; uint8_t v_suppressElabErrors_1337_; lean_object* v_inheritedTraceOptions_1338_; lean_object* v_env_1339_; lean_object* v___x_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v_fileName_1348_; lean_object* v_fileMap_1349_; lean_object* v_currRecDepth_1350_; lean_object* v_ref_1351_; lean_object* v_currNamespace_1352_; lean_object* v_openDecls_1353_; lean_object* v_initHeartbeats_1354_; lean_object* v_maxHeartbeats_1355_; lean_object* v_quotContext_1356_; lean_object* v_currMacroScope_1357_; lean_object* v_cancelTk_x3f_1358_; uint8_t v_suppressElabErrors_1359_; lean_object* v_inheritedTraceOptions_1360_; lean_object* v___y_1361_; uint8_t v___y_1367_; uint8_t v___x_1389_; 
v___x_1324_ = lean_st_ref_get(v_a_1322_);
v_fileName_1325_ = lean_ctor_get(v_a_1321_, 0);
v_fileMap_1326_ = lean_ctor_get(v_a_1321_, 1);
v_options_1327_ = lean_ctor_get(v_a_1321_, 2);
v_currRecDepth_1328_ = lean_ctor_get(v_a_1321_, 3);
v_ref_1329_ = lean_ctor_get(v_a_1321_, 5);
v_currNamespace_1330_ = lean_ctor_get(v_a_1321_, 6);
v_openDecls_1331_ = lean_ctor_get(v_a_1321_, 7);
v_initHeartbeats_1332_ = lean_ctor_get(v_a_1321_, 8);
v_maxHeartbeats_1333_ = lean_ctor_get(v_a_1321_, 9);
v_quotContext_1334_ = lean_ctor_get(v_a_1321_, 10);
v_currMacroScope_1335_ = lean_ctor_get(v_a_1321_, 11);
v_cancelTk_x3f_1336_ = lean_ctor_get(v_a_1321_, 12);
v_suppressElabErrors_1337_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1338_ = lean_ctor_get(v_a_1321_, 13);
v_env_1339_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_env_1339_);
lean_dec(v___x_1324_);
v___x_1340_ = lean_box(v_useRefine_1318_);
v___f_1341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1341_, 0, v_e_1317_);
lean_closure_set(v___f_1341_, 1, v___x_1340_);
v___x_1342_ = l_Lean_pp_mvars;
v___x_1343_ = 0;
lean_inc_ref(v_options_1327_);
v___x_1344_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_1327_, v___x_1342_, v___x_1343_);
v___x_1345_ = l_Lean_diagnostics;
v___x_1346_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_1344_, v___x_1345_);
v___x_1389_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1339_);
lean_dec_ref(v_env_1339_);
if (v___x_1389_ == 0)
{
if (v___x_1346_ == 0)
{
uint8_t v___x_1390_; 
v___x_1390_ = 1;
v___y_1367_ = v___x_1390_;
goto v___jp_1366_;
}
else
{
v___y_1367_ = v___x_1389_;
goto v___jp_1366_;
}
}
else
{
v___y_1367_ = v___x_1346_;
goto v___jp_1366_;
}
v___jp_1347_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1362_ = l_Lean_maxRecDepth;
v___x_1363_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_1344_, v___x_1362_);
lean_inc_ref(v_inheritedTraceOptions_1360_);
lean_inc(v_cancelTk_x3f_1358_);
lean_inc(v_currMacroScope_1357_);
lean_inc(v_quotContext_1356_);
lean_inc(v_maxHeartbeats_1355_);
lean_inc(v_initHeartbeats_1354_);
lean_inc(v_openDecls_1353_);
lean_inc(v_currNamespace_1352_);
lean_inc(v_ref_1351_);
lean_inc(v_currRecDepth_1350_);
lean_inc_ref(v_fileMap_1349_);
lean_inc_ref(v_fileName_1348_);
v___x_1364_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1364_, 0, v_fileName_1348_);
lean_ctor_set(v___x_1364_, 1, v_fileMap_1349_);
lean_ctor_set(v___x_1364_, 2, v___x_1344_);
lean_ctor_set(v___x_1364_, 3, v_currRecDepth_1350_);
lean_ctor_set(v___x_1364_, 4, v___x_1363_);
lean_ctor_set(v___x_1364_, 5, v_ref_1351_);
lean_ctor_set(v___x_1364_, 6, v_currNamespace_1352_);
lean_ctor_set(v___x_1364_, 7, v_openDecls_1353_);
lean_ctor_set(v___x_1364_, 8, v_initHeartbeats_1354_);
lean_ctor_set(v___x_1364_, 9, v_maxHeartbeats_1355_);
lean_ctor_set(v___x_1364_, 10, v_quotContext_1356_);
lean_ctor_set(v___x_1364_, 11, v_currMacroScope_1357_);
lean_ctor_set(v___x_1364_, 12, v_cancelTk_x3f_1358_);
lean_ctor_set(v___x_1364_, 13, v_inheritedTraceOptions_1360_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*14, v___x_1346_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*14 + 1, v_suppressElabErrors_1359_);
v___x_1365_ = l_Lean_Meta_withExposedNames___redArg(v___f_1341_, v_a_1319_, v_a_1320_, v___x_1364_, v___y_1361_);
lean_dec_ref_known(v___x_1364_, 14);
return v___x_1365_;
}
v___jp_1366_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_bool_not(v___y_1367_);
if (v___x_1368_ == 0)
{
v_fileName_1348_ = v_fileName_1325_;
v_fileMap_1349_ = v_fileMap_1326_;
v_currRecDepth_1350_ = v_currRecDepth_1328_;
v_ref_1351_ = v_ref_1329_;
v_currNamespace_1352_ = v_currNamespace_1330_;
v_openDecls_1353_ = v_openDecls_1331_;
v_initHeartbeats_1354_ = v_initHeartbeats_1332_;
v_maxHeartbeats_1355_ = v_maxHeartbeats_1333_;
v_quotContext_1356_ = v_quotContext_1334_;
v_currMacroScope_1357_ = v_currMacroScope_1335_;
v_cancelTk_x3f_1358_ = v_cancelTk_x3f_1336_;
v_suppressElabErrors_1359_ = v_suppressElabErrors_1337_;
v_inheritedTraceOptions_1360_ = v_inheritedTraceOptions_1338_;
v___y_1361_ = v_a_1322_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1369_; lean_object* v_env_1370_; lean_object* v_nextMacroScope_1371_; lean_object* v_ngen_1372_; lean_object* v_auxDeclNGen_1373_; lean_object* v_traceState_1374_; lean_object* v_messages_1375_; lean_object* v_infoState_1376_; lean_object* v_snapshotTasks_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1387_; 
v___x_1369_ = lean_st_ref_take(v_a_1322_);
v_env_1370_ = lean_ctor_get(v___x_1369_, 0);
v_nextMacroScope_1371_ = lean_ctor_get(v___x_1369_, 1);
v_ngen_1372_ = lean_ctor_get(v___x_1369_, 2);
v_auxDeclNGen_1373_ = lean_ctor_get(v___x_1369_, 3);
v_traceState_1374_ = lean_ctor_get(v___x_1369_, 4);
v_messages_1375_ = lean_ctor_get(v___x_1369_, 6);
v_infoState_1376_ = lean_ctor_get(v___x_1369_, 7);
v_snapshotTasks_1377_ = lean_ctor_get(v___x_1369_, 8);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___x_1369_, 5);
lean_dec(v_unused_1388_);
v___x_1379_ = v___x_1369_;
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_snapshotTasks_1377_);
lean_inc(v_infoState_1376_);
lean_inc(v_messages_1375_);
lean_inc(v_traceState_1374_);
lean_inc(v_auxDeclNGen_1373_);
lean_inc(v_ngen_1372_);
lean_inc(v_nextMacroScope_1371_);
lean_inc(v_env_1370_);
lean_dec(v___x_1369_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = l_Lean_Kernel_enableDiag(v_env_1370_, v___x_1346_);
v___x_1382_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 5, v___x_1382_);
lean_ctor_set(v___x_1379_, 0, v___x_1381_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_nextMacroScope_1371_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_ngen_1372_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_auxDeclNGen_1373_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_traceState_1374_);
lean_ctor_set(v_reuseFailAlloc_1386_, 5, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1386_, 6, v_messages_1375_);
lean_ctor_set(v_reuseFailAlloc_1386_, 7, v_infoState_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 8, v_snapshotTasks_1377_);
v___x_1384_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_st_ref_set(v_a_1322_, v___x_1384_);
v_fileName_1348_ = v_fileName_1325_;
v_fileMap_1349_ = v_fileMap_1326_;
v_currRecDepth_1350_ = v_currRecDepth_1328_;
v_ref_1351_ = v_ref_1329_;
v_currNamespace_1352_ = v_currNamespace_1330_;
v_openDecls_1353_ = v_openDecls_1331_;
v_initHeartbeats_1354_ = v_initHeartbeats_1332_;
v_maxHeartbeats_1355_ = v_maxHeartbeats_1333_;
v_quotContext_1356_ = v_quotContext_1334_;
v_currMacroScope_1357_ = v_currMacroScope_1335_;
v_cancelTk_x3f_1358_ = v_cancelTk_x3f_1336_;
v_suppressElabErrors_1359_ = v_suppressElabErrors_1337_;
v_inheritedTraceOptions_1360_ = v_inheritedTraceOptions_1338_;
v___y_1361_ = v_a_1322_;
goto v___jp_1347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* v_e_1391_, lean_object* v_useRefine_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
uint8_t v_useRefine_boxed_1398_; lean_object* v_res_1399_; 
v_useRefine_boxed_1398_ = lean_unbox(v_useRefine_1392_);
v_res_1399_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1391_, v_useRefine_boxed_1398_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(lean_object* v_as_1403_, size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_b_1406_);
return v___x_1413_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_array_uget_borrowed(v_as_1403_, v_i_1405_);
lean_inc(v_a_1414_);
v___x_1415_ = l_Lean_MVarId_getType(v_a_1414_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_1416_, v___y_1408_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___boxed), 6, 1);
lean_closure_set(v___x_1419_, 0, v_a_1418_);
v___x_1420_ = l_Lean_Meta_withExposedNames___redArg(v___x_1419_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1));
v___x_1423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v_a_1421_);
v___x_1424_ = l_Std_Format_defWidth;
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = l_Std_Format_pretty(v___x_1423_, v___x_1424_, v___x_1425_, v___x_1425_);
v___x_1427_ = lean_string_append(v_b_1406_, v___x_1426_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_i_1405_, v___x_1428_);
v_i_1405_ = v___x_1429_;
v_b_1406_ = v___x_1427_;
goto _start;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_b_1406_);
v_a_1431_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1420_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1420_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_b_1406_);
v_a_1439_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1417_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1417_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_b_1406_);
v_a_1447_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1415_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1415_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(lean_object* v_as_1455_, lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
size_t v_sz_boxed_1464_; size_t v_i_boxed_1465_; lean_object* v_res_1466_; 
v_sz_boxed_1464_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1455_, v_sz_boxed_1464_, v_i_boxed_1465_, v_b_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_as_1455_);
return v_res_1466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5));
v___x_1476_ = l_Lean_stringToMessageData(v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t v_addSubgoalsMsg_1478_, lean_object* v_checkState_x3f_1479_, lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v_postInfo_x3f_1493_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___x_1534_; lean_object* v_fileName_1535_; lean_object* v_fileMap_1536_; lean_object* v_options_1537_; lean_object* v_currRecDepth_1538_; lean_object* v_ref_1539_; lean_object* v_currNamespace_1540_; lean_object* v_openDecls_1541_; lean_object* v_initHeartbeats_1542_; lean_object* v_maxHeartbeats_1543_; lean_object* v_quotContext_1544_; lean_object* v_currMacroScope_1545_; lean_object* v_cancelTk_x3f_1546_; uint8_t v_suppressElabErrors_1547_; lean_object* v_inheritedTraceOptions_1548_; lean_object* v_env_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v_fileName_1556_; lean_object* v_fileMap_1557_; lean_object* v_currRecDepth_1558_; lean_object* v_ref_1559_; lean_object* v_currNamespace_1560_; lean_object* v_openDecls_1561_; lean_object* v_initHeartbeats_1562_; lean_object* v_maxHeartbeats_1563_; lean_object* v_quotContext_1564_; lean_object* v_currMacroScope_1565_; lean_object* v_cancelTk_x3f_1566_; uint8_t v_suppressElabErrors_1567_; lean_object* v_inheritedTraceOptions_1568_; lean_object* v___y_1569_; uint8_t v___y_1649_; uint8_t v___x_1671_; 
v___x_1534_ = lean_st_ref_get(v_a_1488_);
v_fileName_1535_ = lean_ctor_get(v_a_1487_, 0);
v_fileMap_1536_ = lean_ctor_get(v_a_1487_, 1);
v_options_1537_ = lean_ctor_get(v_a_1487_, 2);
v_currRecDepth_1538_ = lean_ctor_get(v_a_1487_, 3);
v_ref_1539_ = lean_ctor_get(v_a_1487_, 5);
v_currNamespace_1540_ = lean_ctor_get(v_a_1487_, 6);
v_openDecls_1541_ = lean_ctor_get(v_a_1487_, 7);
v_initHeartbeats_1542_ = lean_ctor_get(v_a_1487_, 8);
v_maxHeartbeats_1543_ = lean_ctor_get(v_a_1487_, 9);
v_quotContext_1544_ = lean_ctor_get(v_a_1487_, 10);
v_currMacroScope_1545_ = lean_ctor_get(v_a_1487_, 11);
v_cancelTk_x3f_1546_ = lean_ctor_get(v_a_1487_, 12);
v_suppressElabErrors_1547_ = lean_ctor_get_uint8(v_a_1487_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1548_ = lean_ctor_get(v_a_1487_, 13);
v_env_1549_ = lean_ctor_get(v___x_1534_, 0);
lean_inc_ref(v_env_1549_);
lean_dec(v___x_1534_);
v___x_1550_ = l_Lean_pp_mvars;
v___x_1551_ = 0;
lean_inc_ref(v_options_1537_);
v___x_1552_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_1537_, v___x_1550_, v___x_1551_);
v___x_1553_ = l_Lean_diagnostics;
v___x_1554_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_1552_, v___x_1553_);
v___x_1671_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1549_);
lean_dec_ref(v_env_1549_);
if (v___x_1671_ == 0)
{
if (v___x_1554_ == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = 1;
v___y_1649_ = v___x_1672_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v___x_1671_;
goto v___jp_1648_;
}
}
else
{
v___y_1649_ = v___x_1554_;
goto v___jp_1648_;
}
v___jp_1490_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___y_1492_);
v___x_1496_ = lean_box(0);
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___y_1491_);
v___x_1498_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1495_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
lean_ctor_set(v___x_1498_, 2, v_postInfo_x3f_1493_);
lean_ctor_set(v___x_1498_, 3, v___x_1496_);
lean_ctor_set(v___x_1498_, 4, v___x_1497_);
lean_ctor_set(v___x_1498_, 5, v___x_1496_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
v___jp_1501_:
{
if (v___y_1507_ == 0)
{
lean_object* v___x_1508_; size_t v_sz_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2));
v_sz_1509_ = lean_array_size(v___y_1503_);
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v___y_1503_, v_sz_1509_, v___x_1510_, v___x_1508_, v_a_1485_, v_a_1486_, v___y_1504_, v___y_1506_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v___y_1503_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_a_1512_);
v___y_1491_ = v___y_1502_;
v___y_1492_ = v___y_1505_;
v_postInfo_x3f_1493_ = v___x_1513_;
goto v___jp_1490_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1502_);
v_a_1514_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1511_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1511_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v___x_1522_; 
lean_dec_ref(v___y_1504_);
lean_dec_ref(v___y_1503_);
v___x_1522_ = lean_box(0);
v___y_1491_ = v___y_1502_;
v___y_1492_ = v___y_1505_;
v_postInfo_x3f_1493_ = v___x_1522_;
goto v___jp_1490_;
}
}
v___jp_1523_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc_ref(v___y_1526_);
v___x_1527_ = l_Lean_stringToMessageData(v___y_1526_);
lean_inc_ref(v___y_1525_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___y_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_1530_, v___y_1524_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
v___jp_1555_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = l_Lean_maxRecDepth;
v___x_1571_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_1552_, v___x_1570_);
lean_inc_ref(v_inheritedTraceOptions_1568_);
lean_inc(v_cancelTk_x3f_1566_);
lean_inc(v_currMacroScope_1565_);
lean_inc(v_quotContext_1564_);
lean_inc(v_maxHeartbeats_1563_);
lean_inc(v_initHeartbeats_1562_);
lean_inc(v_openDecls_1561_);
lean_inc(v_currNamespace_1560_);
lean_inc(v_ref_1559_);
lean_inc(v_currRecDepth_1558_);
lean_inc_ref(v_fileMap_1557_);
lean_inc_ref(v_fileName_1556_);
v___x_1572_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1572_, 0, v_fileName_1556_);
lean_ctor_set(v___x_1572_, 1, v_fileMap_1557_);
lean_ctor_set(v___x_1572_, 2, v___x_1552_);
lean_ctor_set(v___x_1572_, 3, v_currRecDepth_1558_);
lean_ctor_set(v___x_1572_, 4, v___x_1571_);
lean_ctor_set(v___x_1572_, 5, v_ref_1559_);
lean_ctor_set(v___x_1572_, 6, v_currNamespace_1560_);
lean_ctor_set(v___x_1572_, 7, v_openDecls_1561_);
lean_ctor_set(v___x_1572_, 8, v_initHeartbeats_1562_);
lean_ctor_set(v___x_1572_, 9, v_maxHeartbeats_1563_);
lean_ctor_set(v___x_1572_, 10, v_quotContext_1564_);
lean_ctor_set(v___x_1572_, 11, v_currMacroScope_1565_);
lean_ctor_set(v___x_1572_, 12, v_cancelTk_x3f_1566_);
lean_ctor_set(v___x_1572_, 13, v_inheritedTraceOptions_1568_);
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*14, v___x_1554_);
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*14 + 1, v_suppressElabErrors_1567_);
lean_inc_ref(v_e_1480_);
v___x_1573_ = l_Lean_Meta_getMVars(v_e_1480_, v_a_1485_, v_a_1486_, v___x_1572_, v___y_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = lean_array_get_size(v_a_1574_);
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = lean_nat_dec_eq(v___x_1575_, v___x_1576_);
v___x_1578_ = lean_bool_not(v___x_1577_);
v___x_1579_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1480_, v___x_1578_, v_a_1485_, v_a_1486_, v___x_1572_, v___y_1569_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1631_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1631_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1631_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
if (lean_obj_tag(v_checkState_x3f_1479_) == 1)
{
lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1582_);
v_fst_1584_ = lean_ctor_get(v_a_1580_, 0);
v_snd_1585_ = lean_ctor_get(v_a_1580_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_a_1580_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1587_ = v_a_1580_;
v_isShared_1588_ = v_isSharedCheck_1614_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_inc(v_fst_1584_);
lean_dec(v_a_1580_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1614_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_val_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_val_1589_ = lean_ctor_get(v_checkState_x3f_1479_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_checkState_x3f_1479_, 1);
v___x_1590_ = lean_box(0);
lean_inc(v_snd_1585_);
v___x_1591_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_1584_, v_snd_1585_, v_val_1589_, v___x_1590_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v___x_1572_, v___y_1569_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
if (lean_obj_tag(v_a_1592_) == 1)
{
lean_object* v_val_1593_; lean_object* v_fst_1594_; lean_object* v_snd_1595_; uint8_t v___x_1596_; 
lean_del_object(v___x_1587_);
lean_dec(v_snd_1585_);
v_val_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v_a_1592_, 1);
v_fst_1594_ = lean_ctor_get(v_val_1593_, 0);
lean_inc(v_fst_1594_);
v_snd_1595_ = lean_ctor_get(v_val_1593_, 1);
lean_inc(v_snd_1595_);
lean_dec(v_val_1593_);
v___x_1596_ = lean_bool_not(v_addSubgoalsMsg_1478_);
if (v___x_1596_ == 0)
{
v___y_1502_ = v_snd_1595_;
v___y_1503_ = v_a_1574_;
v___y_1504_ = v___x_1572_;
v___y_1505_ = v_fst_1594_;
v___y_1506_ = v___y_1569_;
v___y_1507_ = v___x_1577_;
goto v___jp_1501_;
}
else
{
v___y_1502_ = v_snd_1595_;
v___y_1503_ = v_a_1574_;
v___y_1504_ = v___x_1572_;
v___y_1505_ = v_fst_1594_;
v___y_1506_ = v___y_1569_;
v___y_1507_ = v___x_1596_;
goto v___jp_1501_;
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_dec(v_a_1592_);
lean_dec(v_a_1574_);
lean_dec_ref_known(v___x_1572_, 14);
v___x_1597_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 7);
lean_ctor_set(v___x_1587_, 0, v___x_1597_);
v___x_1599_ = v___x_1587_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_snd_1585_);
v___x_1599_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6);
if (v___x_1578_ == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_1524_ = v___x_1601_;
v___y_1525_ = v___x_1602_;
v___y_1526_ = v___x_1603_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7));
v___y_1524_ = v___x_1601_;
v___y_1525_ = v___x_1602_;
v___y_1526_ = v___x_1604_;
goto v___jp_1523_;
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_del_object(v___x_1587_);
lean_dec(v_snd_1585_);
lean_dec(v_a_1574_);
lean_dec_ref_known(v___x_1572_, 14);
v_a_1606_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1591_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1591_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v_fst_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1574_);
lean_dec_ref_known(v___x_1572_, 14);
lean_dec(v_checkState_x3f_1479_);
v_fst_1615_ = lean_ctor_get(v_a_1580_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_a_1580_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v_a_1580_, 1);
lean_dec(v_unused_1630_);
v___x_1617_ = v_a_1580_;
v_isShared_1618_ = v_isSharedCheck_1629_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_fst_1615_);
lean_dec(v_a_1580_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1629_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v_fst_1615_);
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_fst_1615_);
v___x_1621_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
lean_ctor_set(v___x_1623_, 2, v___x_1622_);
lean_ctor_set(v___x_1623_, 3, v___x_1622_);
lean_ctor_set(v___x_1623_, 4, v___x_1622_);
lean_ctor_set(v___x_1623_, 5, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1624_);
v___x_1626_ = v___x_1582_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_a_1574_);
lean_dec_ref_known(v___x_1572_, 14);
lean_dec(v_checkState_x3f_1479_);
v_a_1632_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1579_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1579_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref_known(v___x_1572_, 14);
lean_dec_ref(v_e_1480_);
lean_dec(v_checkState_x3f_1479_);
v_a_1640_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1573_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1573_);
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
uint8_t v___x_1650_; 
v___x_1650_ = lean_bool_not(v___y_1649_);
if (v___x_1650_ == 0)
{
v_fileName_1556_ = v_fileName_1535_;
v_fileMap_1557_ = v_fileMap_1536_;
v_currRecDepth_1558_ = v_currRecDepth_1538_;
v_ref_1559_ = v_ref_1539_;
v_currNamespace_1560_ = v_currNamespace_1540_;
v_openDecls_1561_ = v_openDecls_1541_;
v_initHeartbeats_1562_ = v_initHeartbeats_1542_;
v_maxHeartbeats_1563_ = v_maxHeartbeats_1543_;
v_quotContext_1564_ = v_quotContext_1544_;
v_currMacroScope_1565_ = v_currMacroScope_1545_;
v_cancelTk_x3f_1566_ = v_cancelTk_x3f_1546_;
v_suppressElabErrors_1567_ = v_suppressElabErrors_1547_;
v_inheritedTraceOptions_1568_ = v_inheritedTraceOptions_1548_;
v___y_1569_ = v_a_1488_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1651_; lean_object* v_env_1652_; lean_object* v_nextMacroScope_1653_; lean_object* v_ngen_1654_; lean_object* v_auxDeclNGen_1655_; lean_object* v_traceState_1656_; lean_object* v_messages_1657_; lean_object* v_infoState_1658_; lean_object* v_snapshotTasks_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1669_; 
v___x_1651_ = lean_st_ref_take(v_a_1488_);
v_env_1652_ = lean_ctor_get(v___x_1651_, 0);
v_nextMacroScope_1653_ = lean_ctor_get(v___x_1651_, 1);
v_ngen_1654_ = lean_ctor_get(v___x_1651_, 2);
v_auxDeclNGen_1655_ = lean_ctor_get(v___x_1651_, 3);
v_traceState_1656_ = lean_ctor_get(v___x_1651_, 4);
v_messages_1657_ = lean_ctor_get(v___x_1651_, 6);
v_infoState_1658_ = lean_ctor_get(v___x_1651_, 7);
v_snapshotTasks_1659_ = lean_ctor_get(v___x_1651_, 8);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v___x_1651_, 5);
lean_dec(v_unused_1670_);
v___x_1661_ = v___x_1651_;
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_snapshotTasks_1659_);
lean_inc(v_infoState_1658_);
lean_inc(v_messages_1657_);
lean_inc(v_traceState_1656_);
lean_inc(v_auxDeclNGen_1655_);
lean_inc(v_ngen_1654_);
lean_inc(v_nextMacroScope_1653_);
lean_inc(v_env_1652_);
lean_dec(v___x_1651_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1663_ = l_Lean_Kernel_enableDiag(v_env_1652_, v___x_1554_);
v___x_1664_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 5, v___x_1664_);
lean_ctor_set(v___x_1661_, 0, v___x_1663_);
v___x_1666_ = v___x_1661_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_nextMacroScope_1653_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_ngen_1654_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_auxDeclNGen_1655_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_traceState_1656_);
lean_ctor_set(v_reuseFailAlloc_1668_, 5, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1668_, 6, v_messages_1657_);
lean_ctor_set(v_reuseFailAlloc_1668_, 7, v_infoState_1658_);
lean_ctor_set(v_reuseFailAlloc_1668_, 8, v_snapshotTasks_1659_);
v___x_1666_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_st_ref_set(v_a_1488_, v___x_1666_);
v_fileName_1556_ = v_fileName_1535_;
v_fileMap_1557_ = v_fileMap_1536_;
v_currRecDepth_1558_ = v_currRecDepth_1538_;
v_ref_1559_ = v_ref_1539_;
v_currNamespace_1560_ = v_currNamespace_1540_;
v_openDecls_1561_ = v_openDecls_1541_;
v_initHeartbeats_1562_ = v_initHeartbeats_1542_;
v_maxHeartbeats_1563_ = v_maxHeartbeats_1543_;
v_quotContext_1564_ = v_quotContext_1544_;
v_currMacroScope_1565_ = v_currMacroScope_1545_;
v_cancelTk_x3f_1566_ = v_cancelTk_x3f_1546_;
v_suppressElabErrors_1567_ = v_suppressElabErrors_1547_;
v_inheritedTraceOptions_1568_ = v_inheritedTraceOptions_1548_;
v___y_1569_ = v_a_1488_;
goto v___jp_1555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* v_addSubgoalsMsg_1673_, lean_object* v_checkState_x3f_1674_, lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1685_; lean_object* v_res_1686_; 
v_addSubgoalsMsg_boxed_1685_ = lean_unbox(v_addSubgoalsMsg_1673_);
v_res_1686_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_boxed_1685_, v_checkState_x3f_1674_, v_e_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object* v_as_1687_, size_t v_sz_1688_, size_t v_i_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1687_, v_sz_1688_, v_i_1689_, v_b_1690_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object* v_as_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
size_t v_sz_boxed_1714_; size_t v_i_boxed_1715_; lean_object* v_res_1716_; 
v_sz_boxed_1714_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_1701_, v_sz_boxed_1714_, v_i_boxed_1715_, v_b_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec_ref(v_as_1701_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1717_, lean_object* v_msgData_1718_, uint8_t v_severity_1719_, uint8_t v_isSilent_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1763_; lean_object* v___y_1764_; uint8_t v___y_1765_; uint8_t v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1788_; lean_object* v___y_1789_; uint8_t v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; uint8_t v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; uint8_t v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1804_; uint8_t v___y_1805_; uint8_t v___x_1810_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; uint8_t v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; uint8_t v___y_1818_; uint8_t v___y_1820_; uint8_t v___x_1835_; 
v___x_1810_ = 2;
v___x_1835_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1719_, v___x_1810_);
if (v___x_1835_ == 0)
{
v___y_1820_ = v___x_1835_;
goto v___jp_1819_;
}
else
{
uint8_t v___x_1836_; 
lean_inc_ref(v_msgData_1718_);
v___x_1836_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1718_);
v___y_1820_ = v___x_1836_;
goto v___jp_1819_;
}
v___jp_1726_:
{
lean_object* v___x_1736_; lean_object* v_currNamespace_1737_; lean_object* v_openDecls_1738_; lean_object* v_env_1739_; lean_object* v_nextMacroScope_1740_; lean_object* v_ngen_1741_; lean_object* v_auxDeclNGen_1742_; lean_object* v_traceState_1743_; lean_object* v_cache_1744_; lean_object* v_messages_1745_; lean_object* v_infoState_1746_; lean_object* v_snapshotTasks_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1761_; 
v___x_1736_ = lean_st_ref_take(v___y_1735_);
v_currNamespace_1737_ = lean_ctor_get(v___y_1734_, 6);
v_openDecls_1738_ = lean_ctor_get(v___y_1734_, 7);
v_env_1739_ = lean_ctor_get(v___x_1736_, 0);
v_nextMacroScope_1740_ = lean_ctor_get(v___x_1736_, 1);
v_ngen_1741_ = lean_ctor_get(v___x_1736_, 2);
v_auxDeclNGen_1742_ = lean_ctor_get(v___x_1736_, 3);
v_traceState_1743_ = lean_ctor_get(v___x_1736_, 4);
v_cache_1744_ = lean_ctor_get(v___x_1736_, 5);
v_messages_1745_ = lean_ctor_get(v___x_1736_, 6);
v_infoState_1746_ = lean_ctor_get(v___x_1736_, 7);
v_snapshotTasks_1747_ = lean_ctor_get(v___x_1736_, 8);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1749_ = v___x_1736_;
v_isShared_1750_ = v_isSharedCheck_1761_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_snapshotTasks_1747_);
lean_inc(v_infoState_1746_);
lean_inc(v_messages_1745_);
lean_inc(v_cache_1744_);
lean_inc(v_traceState_1743_);
lean_inc(v_auxDeclNGen_1742_);
lean_inc(v_ngen_1741_);
lean_inc(v_nextMacroScope_1740_);
lean_inc(v_env_1739_);
lean_dec(v___x_1736_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1761_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_inc(v_openDecls_1738_);
lean_inc(v_currNamespace_1737_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_currNamespace_1737_);
lean_ctor_set(v___x_1751_, 1, v_openDecls_1738_);
v___x_1752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___y_1730_);
lean_inc_ref(v___y_1728_);
lean_inc_ref(v___y_1733_);
v___x_1753_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1753_, 0, v___y_1733_);
lean_ctor_set(v___x_1753_, 1, v___y_1729_);
lean_ctor_set(v___x_1753_, 2, v___y_1727_);
lean_ctor_set(v___x_1753_, 3, v___y_1728_);
lean_ctor_set(v___x_1753_, 4, v___x_1752_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*5, v___y_1731_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*5 + 1, v___y_1732_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*5 + 2, v_isSilent_1720_);
v___x_1754_ = l_Lean_MessageLog_add(v___x_1753_, v_messages_1745_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 6, v___x_1754_);
v___x_1756_ = v___x_1749_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_env_1739_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_nextMacroScope_1740_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_ngen_1741_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_auxDeclNGen_1742_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_traceState_1743_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v_cache_1744_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_infoState_1746_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_snapshotTasks_1747_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_st_ref_set(v___y_1735_, v___x_1756_);
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
v___jp_1762_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1786_; 
v___x_1771_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1718_);
v___x_1772_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1771_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1786_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1786_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_inc_ref_n(v___y_1764_, 2);
v___x_1777_ = l_Lean_FileMap_toPosition(v___y_1764_, v___y_1767_);
lean_dec(v___y_1767_);
v___x_1778_ = l_Lean_FileMap_toPosition(v___y_1764_, v___y_1770_);
lean_dec(v___y_1770_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_1765_ == 0)
{
lean_del_object(v___x_1775_);
lean_dec_ref(v___y_1763_);
v___y_1727_ = v___x_1779_;
v___y_1728_ = v___x_1780_;
v___y_1729_ = v___x_1777_;
v___y_1730_ = v_a_1773_;
v___y_1731_ = v___y_1766_;
v___y_1732_ = v___y_1769_;
v___y_1733_ = v___y_1768_;
v___y_1734_ = v___y_1723_;
v___y_1735_ = v___y_1724_;
goto v___jp_1726_;
}
else
{
uint8_t v___x_1781_; 
lean_inc(v_a_1773_);
v___x_1781_ = l_Lean_MessageData_hasTag(v___y_1763_, v_a_1773_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
lean_dec_ref_known(v___x_1779_, 1);
lean_dec_ref(v___x_1777_);
lean_dec(v_a_1773_);
v___x_1782_ = lean_box(0);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1782_);
v___x_1784_ = v___x_1775_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
else
{
lean_del_object(v___x_1775_);
v___y_1727_ = v___x_1779_;
v___y_1728_ = v___x_1780_;
v___y_1729_ = v___x_1777_;
v___y_1730_ = v_a_1773_;
v___y_1731_ = v___y_1766_;
v___y_1732_ = v___y_1769_;
v___y_1733_ = v___y_1768_;
v___y_1734_ = v___y_1723_;
v___y_1735_ = v___y_1724_;
goto v___jp_1726_;
}
}
}
}
v___jp_1787_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Syntax_getTailPos_x3f(v___y_1791_, v___y_1792_);
lean_dec(v___y_1791_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_inc(v___y_1795_);
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___y_1789_;
v___y_1765_ = v___y_1790_;
v___y_1766_ = v___y_1792_;
v___y_1767_ = v___y_1795_;
v___y_1768_ = v___y_1794_;
v___y_1769_ = v___y_1793_;
v___y_1770_ = v___y_1795_;
goto v___jp_1762_;
}
else
{
lean_object* v_val_1797_; 
v_val_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___y_1789_;
v___y_1765_ = v___y_1790_;
v___y_1766_ = v___y_1792_;
v___y_1767_ = v___y_1795_;
v___y_1768_ = v___y_1794_;
v___y_1769_ = v___y_1793_;
v___y_1770_ = v_val_1797_;
goto v___jp_1762_;
}
}
v___jp_1798_:
{
lean_object* v_ref_1806_; lean_object* v___x_1807_; 
v_ref_1806_ = l_Lean_replaceRef(v_ref_1717_, v___y_1800_);
v___x_1807_ = l_Lean_Syntax_getPos_x3f(v_ref_1806_, v___y_1803_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_unsigned_to_nat(0u);
v___y_1788_ = v___y_1799_;
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1802_;
v___y_1791_ = v_ref_1806_;
v___y_1792_ = v___y_1803_;
v___y_1793_ = v___y_1805_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v___x_1808_;
goto v___jp_1787_;
}
else
{
lean_object* v_val_1809_; 
v_val_1809_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_val_1809_);
lean_dec_ref_known(v___x_1807_, 1);
v___y_1788_ = v___y_1799_;
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1802_;
v___y_1791_ = v_ref_1806_;
v___y_1792_ = v___y_1803_;
v___y_1793_ = v___y_1805_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_val_1809_;
goto v___jp_1787_;
}
}
v___jp_1811_:
{
if (v___y_1818_ == 0)
{
v___y_1799_ = v___y_1814_;
v___y_1800_ = v___y_1812_;
v___y_1801_ = v___y_1813_;
v___y_1802_ = v___y_1815_;
v___y_1803_ = v___y_1817_;
v___y_1804_ = v___y_1816_;
v___y_1805_ = v_severity_1719_;
goto v___jp_1798_;
}
else
{
v___y_1799_ = v___y_1814_;
v___y_1800_ = v___y_1812_;
v___y_1801_ = v___y_1813_;
v___y_1802_ = v___y_1815_;
v___y_1803_ = v___y_1817_;
v___y_1804_ = v___y_1816_;
v___y_1805_ = v___x_1810_;
goto v___jp_1798_;
}
}
v___jp_1819_:
{
if (v___y_1820_ == 0)
{
lean_object* v_fileName_1821_; lean_object* v_fileMap_1822_; lean_object* v_options_1823_; lean_object* v_ref_1824_; uint8_t v_suppressElabErrors_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; uint8_t v___x_1829_; uint8_t v___x_1830_; 
v_fileName_1821_ = lean_ctor_get(v___y_1723_, 0);
v_fileMap_1822_ = lean_ctor_get(v___y_1723_, 1);
v_options_1823_ = lean_ctor_get(v___y_1723_, 2);
v_ref_1824_ = lean_ctor_get(v___y_1723_, 5);
v_suppressElabErrors_1825_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*14 + 1);
v___x_1826_ = lean_box(v___y_1820_);
v___x_1827_ = lean_box(v_suppressElabErrors_1825_);
v___f_1828_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1828_, 0, v___x_1826_);
lean_closure_set(v___f_1828_, 1, v___x_1827_);
v___x_1829_ = 1;
v___x_1830_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1719_, v___x_1829_);
if (v___x_1830_ == 0)
{
v___y_1812_ = v_ref_1824_;
v___y_1813_ = v_fileMap_1822_;
v___y_1814_ = v___f_1828_;
v___y_1815_ = v_suppressElabErrors_1825_;
v___y_1816_ = v_fileName_1821_;
v___y_1817_ = v___y_1820_;
v___y_1818_ = v___x_1830_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = l_Lean_warningAsError;
v___x_1832_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1823_, v___x_1831_);
v___y_1812_ = v_ref_1824_;
v___y_1813_ = v_fileMap_1822_;
v___y_1814_ = v___f_1828_;
v___y_1815_ = v_suppressElabErrors_1825_;
v___y_1816_ = v_fileName_1821_;
v___y_1817_ = v___y_1820_;
v___y_1818_ = v___x_1832_;
goto v___jp_1811_;
}
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec_ref(v_msgData_1718_);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1837_, lean_object* v_msgData_1838_, lean_object* v_severity_1839_, lean_object* v_isSilent_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
uint8_t v_severity_boxed_1846_; uint8_t v_isSilent_boxed_1847_; lean_object* v_res_1848_; 
v_severity_boxed_1846_ = lean_unbox(v_severity_1839_);
v_isSilent_boxed_1847_ = lean_unbox(v_isSilent_1840_);
v_res_1848_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1837_, v_msgData_1838_, v_severity_boxed_1846_, v_isSilent_boxed_1847_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v_ref_1837_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(lean_object* v_msgData_1849_, uint8_t v_severity_1850_, uint8_t v_isSilent_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_ref_1861_; lean_object* v___x_1862_; 
v_ref_1861_ = lean_ctor_get(v___y_1858_, 5);
v___x_1862_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1861_, v_msgData_1849_, v_severity_1850_, v_isSilent_1851_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(lean_object* v_msgData_1863_, lean_object* v_severity_1864_, lean_object* v_isSilent_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
uint8_t v_severity_boxed_1875_; uint8_t v_isSilent_boxed_1876_; lean_object* v_res_1877_; 
v_severity_boxed_1875_ = lean_unbox(v_severity_1864_);
v_isSilent_boxed_1876_ = lean_unbox(v_isSilent_1865_);
v_res_1877_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1863_, v_severity_boxed_1875_, v_isSilent_boxed_1876_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object* v_msgData_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = 0;
v___x_1889_ = 0;
v___x_1890_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1878_, v___x_1888_, v___x_1889_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object* v_msgData_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_msgData_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* v_ref_1903_, lean_object* v_e_1904_, lean_object* v_origSpan_x3f_1905_, uint8_t v_addSubgoalsMsg_1906_, lean_object* v_codeActionPrefix_x3f_1907_, lean_object* v_checkState_x3f_1908_, uint8_t v_tacticErrorAsInfo_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_1906_, v_checkState_x3f_1908_, v_e_1904_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
if (lean_obj_tag(v_a_1920_) == 0)
{
lean_object* v_val_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_val_1921_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v_a_1920_, 1);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_1923_ = 4;
v___x_1924_ = l_Lean_MessageData_nil;
v___x_1925_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_1903_, v_val_1921_, v_origSpan_x3f_1905_, v___x_1922_, v_codeActionPrefix_x3f_1907_, v___x_1923_, v___x_1924_, v_a_1916_, v_a_1917_);
return v___x_1925_;
}
else
{
lean_dec(v_codeActionPrefix_x3f_1907_);
lean_dec(v_origSpan_x3f_1905_);
lean_dec(v_ref_1903_);
if (v_tacticErrorAsInfo_1909_ == 0)
{
lean_object* v_val_1926_; lean_object* v___x_1927_; 
v_val_1926_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v_a_1920_, 1);
v___x_1927_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_1926_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1927_;
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1929_; 
v_val_1928_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_a_1920_, 1);
v___x_1929_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_val_1928_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_codeActionPrefix_x3f_1907_);
lean_dec(v_origSpan_x3f_1905_);
lean_dec(v_ref_1903_);
v_a_1930_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1919_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1919_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* v_ref_1938_, lean_object* v_e_1939_, lean_object* v_origSpan_x3f_1940_, lean_object* v_addSubgoalsMsg_1941_, lean_object* v_codeActionPrefix_x3f_1942_, lean_object* v_checkState_x3f_1943_, lean_object* v_tacticErrorAsInfo_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1954_; uint8_t v_tacticErrorAsInfo_boxed_1955_; lean_object* v_res_1956_; 
v_addSubgoalsMsg_boxed_1954_ = lean_unbox(v_addSubgoalsMsg_1941_);
v_tacticErrorAsInfo_boxed_1955_ = lean_unbox(v_tacticErrorAsInfo_1944_);
v_res_1956_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_ref_1938_, v_e_1939_, v_origSpan_x3f_1940_, v_addSubgoalsMsg_boxed_1954_, v_codeActionPrefix_x3f_1942_, v_checkState_x3f_1943_, v_tacticErrorAsInfo_boxed_1955_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(lean_object* v_ref_1957_, lean_object* v_msgData_1958_, uint8_t v_severity_1959_, uint8_t v_isSilent_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1957_, v_msgData_1958_, v_severity_1959_, v_isSilent_1960_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1971_, lean_object* v_msgData_1972_, lean_object* v_severity_1973_, lean_object* v_isSilent_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
uint8_t v_severity_boxed_1984_; uint8_t v_isSilent_boxed_1985_; lean_object* v_res_1986_; 
v_severity_boxed_1984_ = lean_unbox(v_severity_1973_);
v_isSilent_boxed_1985_ = lean_unbox(v_isSilent_1974_);
v_res_1986_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_1971_, v_msgData_1972_, v_severity_boxed_1984_, v_isSilent_boxed_1985_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_ref_1971_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(uint8_t v_tacticErrorAsInfo_1987_, lean_object* v_as_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_a_1998_; uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_b_1991_);
return v___x_2003_;
}
else
{
lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2030_; 
v_fst_2004_ = lean_ctor_get(v_b_1991_, 0);
v_snd_2005_ = lean_ctor_get(v_b_1991_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_b_1991_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2007_ = v_b_1991_;
v_isShared_2008_ = v_isSharedCheck_2030_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_dec(v_b_1991_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2030_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_a_2009_; 
v_a_2009_ = lean_array_uget_borrowed(v_as_1988_, v_i_1990_);
if (lean_obj_tag(v_a_2009_) == 0)
{
lean_object* v_val_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v_val_2010_ = lean_ctor_get(v_a_2009_, 0);
lean_inc(v_val_2010_);
v___x_2011_ = lean_array_push(v_fst_2004_, v_val_2010_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_snd_2005_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
v_a_1998_ = v___x_2013_;
goto v___jp_1997_;
}
}
else
{
lean_object* v_val_2015_; 
v_val_2015_ = lean_ctor_get(v_a_2009_, 0);
if (v_tacticErrorAsInfo_1987_ == 0)
{
lean_object* v___x_2021_; 
lean_inc(v_val_2015_);
v___x_2021_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_2015_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_dec_ref_known(v___x_2021_, 1);
goto v___jp_2016_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_del_object(v___x_2007_);
lean_dec(v_snd_2005_);
lean_dec(v_fst_2004_);
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
goto v___jp_2016_;
}
v___jp_2016_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_inc(v_val_2015_);
v___x_2017_ = lean_array_push(v_snd_2005_, v_val_2015_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___x_2017_);
v___x_2019_ = v___x_2007_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_fst_2004_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
v_a_1998_ = v___x_2019_;
goto v___jp_1997_;
}
}
}
}
}
v___jp_1997_:
{
size_t v___x_1999_; size_t v___x_2000_; 
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_add(v_i_1990_, v___x_1999_);
v_i_1990_ = v___x_2000_;
v_b_1991_ = v_a_1998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(lean_object* v_tacticErrorAsInfo_2031_, lean_object* v_as_2032_, lean_object* v_sz_2033_, lean_object* v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2041_; size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_tacticErrorAsInfo_boxed_2041_ = lean_unbox(v_tacticErrorAsInfo_2031_);
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_boxed_2041_, v_as_2032_, v_sz_boxed_2042_, v_i_boxed_2043_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_as_2032_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t v_addSubgoalsMsg_2045_, lean_object* v_checkState_x3f_2046_, size_t v_sz_2047_, size_t v_i_2048_, lean_object* v_bs_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec(v_checkState_x3f_2046_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_bs_2049_);
return v___x_2060_;
}
else
{
lean_object* v_v_2061_; lean_object* v___x_2062_; 
v_v_2061_ = lean_array_uget_borrowed(v_bs_2049_, v_i_2048_);
lean_inc(v_v_2061_);
lean_inc(v_checkState_x3f_2046_);
v___x_2062_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_2045_, v_checkState_x3f_2046_, v_v_2061_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v_bs_x27_2065_; size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = lean_unsigned_to_nat(0u);
v_bs_x27_2065_ = lean_array_uset(v_bs_2049_, v_i_2048_, v___x_2064_);
v___x_2066_ = ((size_t)1ULL);
v___x_2067_ = lean_usize_add(v_i_2048_, v___x_2066_);
v___x_2068_ = lean_array_uset(v_bs_x27_2065_, v_i_2048_, v_a_2063_);
v_i_2048_ = v___x_2067_;
v_bs_2049_ = v___x_2068_;
goto _start;
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_bs_2049_);
lean_dec(v_checkState_x3f_2046_);
v_a_2070_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2062_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2062_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object* v_addSubgoalsMsg_2078_, lean_object* v_checkState_x3f_2079_, lean_object* v_sz_2080_, lean_object* v_i_2081_, lean_object* v_bs_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2092_; size_t v_sz_boxed_2093_; size_t v_i_boxed_2094_; lean_object* v_res_2095_; 
v_addSubgoalsMsg_boxed_2092_ = lean_unbox(v_addSubgoalsMsg_2078_);
v_sz_boxed_2093_ = lean_unbox_usize(v_sz_2080_);
lean_dec(v_sz_2080_);
v_i_boxed_2094_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_boxed_2092_, v_checkState_x3f_2079_, v_sz_boxed_2093_, v_i_boxed_2094_, v_bs_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(lean_object* v_as_2096_, size_t v_sz_2097_, size_t v_i_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_usize_dec_lt(v_i_2098_, v_sz_2097_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_b_2099_);
return v___x_2110_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_array_uget_borrowed(v_as_2096_, v_i_2098_);
lean_inc(v_a_2111_);
v___x_2112_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_a_2111_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; 
lean_dec_ref_known(v___x_2112_, 1);
v___x_2113_ = lean_box(0);
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2098_, v___x_2114_);
v_i_2098_ = v___x_2115_;
v_b_2099_ = v___x_2113_;
goto _start;
}
else
{
return v___x_2112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(lean_object* v_as_2117_, lean_object* v_sz_2118_, lean_object* v_i_2119_, lean_object* v_b_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
size_t v_sz_boxed_2130_; size_t v_i_boxed_2131_; lean_object* v_res_2132_; 
v_sz_boxed_2130_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2131_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_2117_, v_sz_boxed_2130_, v_i_boxed_2131_, v_b_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v_as_2117_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* v_ref_2138_, lean_object* v_es_2139_, lean_object* v_origSpan_x3f_2140_, uint8_t v_addSubgoalsMsg_2141_, lean_object* v_codeActionPrefix_x3f_2142_, lean_object* v_checkState_x3f_2143_, uint8_t v_tacticErrorAsInfo_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
size_t v_sz_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v_sz_2154_ = lean_array_size(v_es_2139_);
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_2141_, v_checkState_x3f_2143_, v_sz_2154_, v___x_2155_, v_es_2139_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; size_t v_sz_2159_; lean_object* v___x_2160_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1));
v_sz_2159_ = lean_array_size(v_a_2157_);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2144_, v_a_2157_, v_sz_2159_, v___x_2155_, v___x_2158_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2157_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v_fst_2162_; lean_object* v_snd_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v_fst_2162_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_fst_2162_);
v_snd_2163_ = lean_ctor_get(v_a_2161_, 1);
lean_inc(v_snd_2163_);
lean_dec(v_a_2161_);
v___x_2164_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2));
v___x_2165_ = 4;
v___x_2166_ = l_Lean_MessageData_nil;
v___x_2167_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2138_, v_fst_2162_, v_origSpan_x3f_2140_, v___x_2164_, v_codeActionPrefix_x3f_2142_, v___x_2165_, v___x_2166_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v___x_2168_; size_t v_sz_2169_; lean_object* v___x_2170_; 
lean_dec_ref_known(v___x_2167_, 1);
v___x_2168_ = lean_box(0);
v_sz_2169_ = lean_array_size(v_snd_2163_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_snd_2163_, v_sz_2169_, v___x_2155_, v___x_2168_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_snd_2163_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v___x_2170_, 0);
lean_dec(v_unused_2178_);
v___x_2172_ = v___x_2170_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_dec(v___x_2170_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2168_);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2168_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
return v___x_2170_;
}
}
else
{
lean_dec(v_snd_2163_);
return v___x_2167_;
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_codeActionPrefix_x3f_2142_);
lean_dec(v_origSpan_x3f_2140_);
lean_dec(v_ref_2138_);
v_a_2179_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2160_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2160_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_codeActionPrefix_x3f_2142_);
lean_dec(v_origSpan_x3f_2140_);
lean_dec(v_ref_2138_);
v_a_2187_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2156_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2156_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* v_ref_2195_, lean_object* v_es_2196_, lean_object* v_origSpan_x3f_2197_, lean_object* v_addSubgoalsMsg_2198_, lean_object* v_codeActionPrefix_x3f_2199_, lean_object* v_checkState_x3f_2200_, lean_object* v_tacticErrorAsInfo_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2211_; uint8_t v_tacticErrorAsInfo_boxed_2212_; lean_object* v_res_2213_; 
v_addSubgoalsMsg_boxed_2211_ = lean_unbox(v_addSubgoalsMsg_2198_);
v_tacticErrorAsInfo_boxed_2212_ = lean_unbox(v_tacticErrorAsInfo_2201_);
v_res_2213_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(v_ref_2195_, v_es_2196_, v_origSpan_x3f_2197_, v_addSubgoalsMsg_boxed_2211_, v_codeActionPrefix_x3f_2199_, v_checkState_x3f_2200_, v_tacticErrorAsInfo_boxed_2212_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t v_tacticErrorAsInfo_2214_, lean_object* v_as_2215_, size_t v_sz_2216_, size_t v_i_2217_, lean_object* v_b_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2214_, v_as_2215_, v_sz_2216_, v_i_2217_, v_b_2218_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object* v_tacticErrorAsInfo_2229_, lean_object* v_as_2230_, lean_object* v_sz_2231_, lean_object* v_i_2232_, lean_object* v_b_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2243_; size_t v_sz_boxed_2244_; size_t v_i_boxed_2245_; lean_object* v_res_2246_; 
v_tacticErrorAsInfo_boxed_2243_ = lean_unbox(v_tacticErrorAsInfo_2229_);
v_sz_boxed_2244_ = lean_unbox_usize(v_sz_2231_);
lean_dec(v_sz_2231_);
v_i_boxed_2245_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_boxed_2243_, v_as_2230_, v_sz_boxed_2244_, v_i_boxed_2245_, v_b_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v_as_2230_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* v_ref_2247_, lean_object* v_e_2248_, lean_object* v_origSpan_x3f_2249_, lean_object* v_header_2250_, lean_object* v_codeActionPrefix_x3f_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_2248_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___x_2259_ = 4;
v___x_2260_ = l_Lean_MessageData_nil;
v___x_2261_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2247_, v_a_2258_, v_origSpan_x3f_2249_, v_header_2250_, v_codeActionPrefix_x3f_2251_, v___x_2259_, v___x_2260_, v_a_2254_, v_a_2255_);
return v___x_2261_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_codeActionPrefix_x3f_2251_);
lean_dec_ref(v_header_2250_);
lean_dec(v_origSpan_x3f_2249_);
lean_dec(v_ref_2247_);
v_a_2262_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2257_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2257_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object* v_ref_2270_, lean_object* v_e_2271_, lean_object* v_origSpan_x3f_2272_, lean_object* v_header_2273_, lean_object* v_codeActionPrefix_x3f_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_ref_2270_, v_e_2271_, v_origSpan_x3f_2272_, v_header_2273_, v_codeActionPrefix_x3f_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t v_sz_2281_, size_t v_i_2282_, lean_object* v_bs_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_usize_dec_lt(v_i_2282_, v_sz_2281_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_bs_2283_);
return v___x_2290_;
}
else
{
lean_object* v_v_2291_; lean_object* v___x_2292_; 
v_v_2291_ = lean_array_uget_borrowed(v_bs_2283_, v_i_2282_);
lean_inc(v_v_2291_);
v___x_2292_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_v_2291_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v_bs_x27_2295_; size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = lean_unsigned_to_nat(0u);
v_bs_x27_2295_ = lean_array_uset(v_bs_2283_, v_i_2282_, v___x_2294_);
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2282_, v___x_2296_);
v___x_2298_ = lean_array_uset(v_bs_x27_2295_, v_i_2282_, v_a_2293_);
v_i_2282_ = v___x_2297_;
v_bs_2283_ = v___x_2298_;
goto _start;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_bs_2283_);
v_a_2300_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2292_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2292_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_bs_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
size_t v_sz_boxed_2316_; size_t v_i_boxed_2317_; lean_object* v_res_2318_; 
v_sz_boxed_2316_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2317_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_boxed_2316_, v_i_boxed_2317_, v_bs_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* v_ref_2319_, lean_object* v_es_2320_, lean_object* v_origSpan_x3f_2321_, lean_object* v_header_2322_, lean_object* v_codeActionPrefix_x3f_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
size_t v_sz_2329_; size_t v___x_2330_; lean_object* v___x_2331_; 
v_sz_2329_ = lean_array_size(v_es_2320_);
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_2329_, v___x_2330_, v_es_2320_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = 4;
v___x_2334_ = l_Lean_MessageData_nil;
v___x_2335_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2319_, v_a_2332_, v_origSpan_x3f_2321_, v_header_2322_, v_codeActionPrefix_x3f_2323_, v___x_2333_, v___x_2334_, v_a_2326_, v_a_2327_);
return v___x_2335_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_codeActionPrefix_x3f_2323_);
lean_dec_ref(v_header_2322_);
lean_dec(v_origSpan_x3f_2321_);
lean_dec(v_ref_2319_);
v_a_2336_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2331_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2331_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object* v_ref_2344_, lean_object* v_es_2345_, lean_object* v_origSpan_x3f_2346_, lean_object* v_header_2347_, lean_object* v_codeActionPrefix_x3f_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(v_ref_2344_, v_es_2345_, v_origSpan_x3f_2346_, v_header_2347_, v_codeActionPrefix_x3f_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2354_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Array_mkArray0(lean_box(0));
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21));
v___x_2404_ = l_Lean_stringToMessageData(v___x_2403_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_2419_ = l_String_toRawSubstring_x27(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84));
v___x_2564_ = l_Lean_stringToMessageData(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object* v_e_2565_, lean_object* v_t_x3f_2566_, uint8_t v_a_2567_, lean_object* v_h_x3f_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___x_2591_; 
lean_inc_ref(v_e_2565_);
v___x_2591_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_2565_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___y_2594_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
if (lean_obj_tag(v_t_x3f_2566_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; 
v_val_2622_ = lean_ctor_get(v_t_x3f_2566_, 0);
lean_inc_n(v_val_2622_, 2);
lean_dec_ref_known(v_t_x3f_2566_, 1);
v___x_2623_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_val_2622_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___y_2626_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
if (v_a_2567_ == 0)
{
if (lean_obj_tag(v_h_x3f_2568_) == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2626_ = v___x_2663_;
goto v___jp_2625_;
}
else
{
lean_object* v_val_2664_; 
v_val_2664_ = lean_ctor_get(v_h_x3f_2568_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v_h_x3f_2568_, 1);
v___y_2626_ = v_val_2664_;
goto v___jp_2625_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2568_) == 0)
{
lean_object* v_ref_2665_; lean_object* v_quotContext_2666_; lean_object* v_currMacroScope_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_ref_2665_ = lean_ctor_get(v___y_2571_, 5);
v_quotContext_2666_ = lean_ctor_get(v___y_2571_, 10);
v_currMacroScope_2667_ = lean_ctor_get(v___y_2571_, 11);
v___x_2668_ = 0;
v___x_2669_ = l_Lean_SourceInfo_fromRef(v_ref_2665_, v___x_2668_);
v___x_2670_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2671_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2669_, 12);
v___x_2672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2669_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2675_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2669_);
lean_ctor_set(v___x_2676_, 1, v___x_2674_);
lean_ctor_set(v___x_2676_, 2, v___x_2675_);
lean_inc_ref(v___x_2676_);
v___x_2677_ = l_Lean_Syntax_node1(v___x_2669_, v___x_2673_, v___x_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2679_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2680_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2681_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2682_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2683_ = lean_box(0);
lean_inc(v_currMacroScope_2667_);
lean_inc(v_quotContext_2666_);
v___x_2684_ = l_Lean_addMacroScope(v_quotContext_2666_, v___x_2683_, v_currMacroScope_2667_);
v___x_2685_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2669_);
lean_ctor_set(v___x_2686_, 1, v___x_2682_);
lean_ctor_set(v___x_2686_, 2, v___x_2684_);
lean_ctor_set(v___x_2686_, 3, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node1(v___x_2669_, v___x_2681_, v___x_2686_);
v___x_2688_ = l_Lean_Syntax_node1(v___x_2669_, v___x_2680_, v___x_2687_);
v___x_2689_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2690_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2669_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2689_, v___x_2691_, v_a_2624_);
v___x_2693_ = l_Lean_Syntax_node1(v___x_2669_, v___x_2674_, v___x_2692_);
v___x_2694_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2669_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_Syntax_node5(v___x_2669_, v___x_2679_, v___x_2688_, v___x_2676_, v___x_2693_, v___x_2695_, v_a_2592_);
v___x_2697_ = l_Lean_Syntax_node1(v___x_2669_, v___x_2678_, v___x_2696_);
v___x_2698_ = l_Lean_Syntax_node3(v___x_2669_, v___x_2670_, v___x_2672_, v___x_2677_, v___x_2697_);
v___x_2699_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81);
v___x_2700_ = l_Lean_MessageData_ofExpr(v_val_2622_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v_fst_2575_ = v___x_2698_;
v_snd_2576_ = v___x_2705_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
v___y_2580_ = v___y_2572_;
goto v___jp_2574_;
}
else
{
lean_object* v_val_2706_; lean_object* v_ref_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v_val_2706_ = lean_ctor_get(v_h_x3f_2568_, 0);
lean_inc_n(v_val_2706_, 2);
lean_dec_ref_known(v_h_x3f_2568_, 1);
v_ref_2707_ = lean_ctor_get(v___y_2571_, 5);
v___x_2708_ = 0;
v___x_2709_ = l_Lean_SourceInfo_fromRef(v_ref_2707_, v___x_2708_);
v___x_2710_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2711_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2709_, 10);
v___x_2712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2709_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2715_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2709_);
lean_ctor_set(v___x_2716_, 1, v___x_2714_);
lean_ctor_set(v___x_2716_, 2, v___x_2715_);
lean_inc_ref(v___x_2716_);
v___x_2717_ = l_Lean_Syntax_node1(v___x_2709_, v___x_2713_, v___x_2716_);
v___x_2718_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2720_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2721_ = l_Lean_mkIdent(v_val_2706_);
v___x_2722_ = l_Lean_Syntax_node1(v___x_2709_, v___x_2720_, v___x_2721_);
v___x_2723_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2724_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2709_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_Syntax_node2(v___x_2709_, v___x_2723_, v___x_2725_, v_a_2624_);
v___x_2727_ = l_Lean_Syntax_node1(v___x_2709_, v___x_2714_, v___x_2726_);
v___x_2728_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2709_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = l_Lean_Syntax_node5(v___x_2709_, v___x_2719_, v___x_2722_, v___x_2716_, v___x_2727_, v___x_2729_, v_a_2592_);
v___x_2731_ = l_Lean_Syntax_node1(v___x_2709_, v___x_2718_, v___x_2730_);
v___x_2732_ = l_Lean_Syntax_node3(v___x_2709_, v___x_2710_, v___x_2712_, v___x_2717_, v___x_2731_);
v___x_2733_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2734_ = l_Lean_MessageData_ofName(v_val_2706_);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = l_Lean_MessageData_ofExpr(v_val_2622_);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v_fst_2575_ = v___x_2732_;
v_snd_2576_ = v___x_2743_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
v___y_2580_ = v___y_2572_;
goto v___jp_2574_;
}
}
v___jp_2625_:
{
lean_object* v_ref_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_ref_2627_ = lean_ctor_get(v___y_2571_, 5);
v___x_2628_ = l_Lean_SourceInfo_fromRef(v_ref_2627_, v_a_2567_);
v___x_2629_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2630_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2628_, 10);
v___x_2631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2628_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2634_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2628_);
lean_ctor_set(v___x_2635_, 1, v___x_2633_);
lean_ctor_set(v___x_2635_, 2, v___x_2634_);
lean_inc_ref(v___x_2635_);
v___x_2636_ = l_Lean_Syntax_node1(v___x_2628_, v___x_2632_, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2638_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2639_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2626_);
v___x_2640_ = l_Lean_mkIdent(v___y_2626_);
v___x_2641_ = l_Lean_Syntax_node1(v___x_2628_, v___x_2639_, v___x_2640_);
v___x_2642_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2643_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2628_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_Syntax_node2(v___x_2628_, v___x_2642_, v___x_2644_, v_a_2624_);
v___x_2646_ = l_Lean_Syntax_node1(v___x_2628_, v___x_2633_, v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2628_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_Syntax_node5(v___x_2628_, v___x_2638_, v___x_2641_, v___x_2635_, v___x_2646_, v___x_2648_, v_a_2592_);
v___x_2650_ = l_Lean_Syntax_node1(v___x_2628_, v___x_2637_, v___x_2649_);
v___x_2651_ = l_Lean_Syntax_node3(v___x_2628_, v___x_2629_, v___x_2631_, v___x_2636_, v___x_2650_);
v___x_2652_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2653_ = l_Lean_MessageData_ofName(v___y_2626_);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_MessageData_ofExpr(v_val_2622_);
v___x_2658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v_fst_2575_ = v___x_2651_;
v_snd_2576_ = v___x_2662_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
v___y_2580_ = v___y_2572_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_val_2622_);
lean_dec(v_a_2592_);
lean_dec_ref(v___y_2571_);
lean_dec(v_h_x3f_2568_);
lean_dec_ref(v_e_2565_);
v_a_2744_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2623_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2623_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_dec(v_t_x3f_2566_);
if (v_a_2567_ == 0)
{
if (lean_obj_tag(v_h_x3f_2568_) == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2594_ = v___x_2752_;
goto v___jp_2593_;
}
else
{
lean_object* v_val_2753_; 
v_val_2753_ = lean_ctor_get(v_h_x3f_2568_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_h_x3f_2568_, 1);
v___y_2594_ = v_val_2753_;
goto v___jp_2593_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2568_) == 0)
{
lean_object* v_ref_2754_; lean_object* v_quotContext_2755_; lean_object* v_currMacroScope_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_ref_2754_ = lean_ctor_get(v___y_2571_, 5);
v_quotContext_2755_ = lean_ctor_get(v___y_2571_, 10);
v_currMacroScope_2756_ = lean_ctor_get(v___y_2571_, 11);
v___x_2757_ = 0;
v___x_2758_ = l_Lean_SourceInfo_fromRef(v_ref_2754_, v___x_2757_);
v___x_2759_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2760_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2758_, 9);
v___x_2761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2758_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2764_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2758_);
lean_ctor_set(v___x_2765_, 1, v___x_2763_);
lean_ctor_set(v___x_2765_, 2, v___x_2764_);
lean_inc_ref_n(v___x_2765_, 2);
v___x_2766_ = l_Lean_Syntax_node1(v___x_2758_, v___x_2762_, v___x_2765_);
v___x_2767_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2768_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2769_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2770_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2771_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2772_ = lean_box(0);
lean_inc(v_currMacroScope_2756_);
lean_inc(v_quotContext_2755_);
v___x_2773_ = l_Lean_addMacroScope(v_quotContext_2755_, v___x_2772_, v_currMacroScope_2756_);
v___x_2774_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2775_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2758_);
lean_ctor_set(v___x_2775_, 1, v___x_2771_);
lean_ctor_set(v___x_2775_, 2, v___x_2773_);
lean_ctor_set(v___x_2775_, 3, v___x_2774_);
v___x_2776_ = l_Lean_Syntax_node1(v___x_2758_, v___x_2770_, v___x_2775_);
v___x_2777_ = l_Lean_Syntax_node1(v___x_2758_, v___x_2769_, v___x_2776_);
v___x_2778_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2758_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_Syntax_node5(v___x_2758_, v___x_2768_, v___x_2777_, v___x_2765_, v___x_2765_, v___x_2779_, v_a_2592_);
v___x_2781_ = l_Lean_Syntax_node1(v___x_2758_, v___x_2767_, v___x_2780_);
v___x_2782_ = l_Lean_Syntax_node3(v___x_2758_, v___x_2759_, v___x_2761_, v___x_2766_, v___x_2781_);
v___x_2783_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85);
v___x_2784_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v_fst_2575_ = v___x_2782_;
v_snd_2576_ = v___x_2785_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
v___y_2580_ = v___y_2572_;
goto v___jp_2574_;
}
else
{
lean_object* v_val_2786_; lean_object* v_ref_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_val_2786_ = lean_ctor_get(v_h_x3f_2568_, 0);
lean_inc_n(v_val_2786_, 2);
lean_dec_ref_known(v_h_x3f_2568_, 1);
v_ref_2787_ = lean_ctor_get(v___y_2571_, 5);
v___x_2788_ = 0;
v___x_2789_ = l_Lean_SourceInfo_fromRef(v_ref_2787_, v___x_2788_);
v___x_2790_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2791_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2789_, 7);
v___x_2792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2789_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2795_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2789_);
lean_ctor_set(v___x_2796_, 1, v___x_2794_);
lean_ctor_set(v___x_2796_, 2, v___x_2795_);
lean_inc_ref_n(v___x_2796_, 2);
v___x_2797_ = l_Lean_Syntax_node1(v___x_2789_, v___x_2793_, v___x_2796_);
v___x_2798_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2799_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2800_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2801_ = l_Lean_mkIdent(v_val_2786_);
v___x_2802_ = l_Lean_Syntax_node1(v___x_2789_, v___x_2800_, v___x_2801_);
v___x_2803_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2789_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_Syntax_node5(v___x_2789_, v___x_2799_, v___x_2802_, v___x_2796_, v___x_2796_, v___x_2804_, v_a_2592_);
v___x_2806_ = l_Lean_Syntax_node1(v___x_2789_, v___x_2798_, v___x_2805_);
v___x_2807_ = l_Lean_Syntax_node3(v___x_2789_, v___x_2790_, v___x_2792_, v___x_2797_, v___x_2806_);
v___x_2808_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2809_ = l_Lean_MessageData_ofName(v_val_2786_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v_fst_2575_ = v___x_2807_;
v_snd_2576_ = v___x_2814_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
v___y_2580_ = v___y_2572_;
goto v___jp_2574_;
}
}
}
v___jp_2593_:
{
lean_object* v_ref_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_ref_2595_ = lean_ctor_get(v___y_2571_, 5);
v___x_2596_ = l_Lean_SourceInfo_fromRef(v_ref_2595_, v_a_2567_);
v___x_2597_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2598_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2596_, 7);
v___x_2599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2602_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2596_);
lean_ctor_set(v___x_2603_, 1, v___x_2601_);
lean_ctor_set(v___x_2603_, 2, v___x_2602_);
lean_inc_ref_n(v___x_2603_, 2);
v___x_2604_ = l_Lean_Syntax_node1(v___x_2596_, v___x_2600_, v___x_2603_);
v___x_2605_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2606_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2607_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2594_);
v___x_2608_ = l_Lean_mkIdent(v___y_2594_);
v___x_2609_ = l_Lean_Syntax_node1(v___x_2596_, v___x_2607_, v___x_2608_);
v___x_2610_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2596_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node5(v___x_2596_, v___x_2606_, v___x_2609_, v___x_2603_, v___x_2603_, v___x_2611_, v_a_2592_);
v___x_2613_ = l_Lean_Syntax_node1(v___x_2596_, v___x_2605_, v___x_2612_);
v___x_2614_ = l_Lean_Syntax_node3(v___x_2596_, v___x_2597_, v___x_2599_, v___x_2604_, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2616_ = l_Lean_MessageData_ofName(v___y_2594_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v_fst_2575_ = v___x_2614_;
v_snd_2576_ = v___x_2621_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
v___y_2580_ = v___y_2572_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v___y_2571_);
lean_dec(v_h_x3f_2568_);
lean_dec(v_t_x3f_2566_);
lean_dec_ref(v_e_2565_);
v_a_2815_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2591_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2591_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
v___jp_2574_:
{
lean_object* v___x_2581_; lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
v___x_2581_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_snd_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref(v___y_2579_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_fst_2575_);
lean_ctor_set(v___x_2586_, 1, v_a_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object* v_e_2823_, lean_object* v_t_x3f_2824_, lean_object* v_a_2825_, lean_object* v_h_x3f_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
uint8_t v_a_17939__boxed_2832_; lean_object* v_res_2833_; 
v_a_17939__boxed_2832_ = lean_unbox(v_a_2825_);
v_res_2833_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(v_e_2823_, v_t_x3f_2824_, v_a_17939__boxed_2832_, v_h_x3f_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2833_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1));
v___x_2838_ = l_Lean_MessageData_ofFormat(v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* v_ref_2839_, lean_object* v_h_x3f_2840_, lean_object* v_t_x3f_2841_, lean_object* v_e_2842_, lean_object* v_origSpan_x3f_2843_, lean_object* v_checkState_x3f_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_tac_2855_; lean_object* v_msg_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___x_2868_; 
lean_inc(v_a_2852_);
lean_inc_ref(v_a_2851_);
lean_inc(v_a_2850_);
lean_inc_ref(v_a_2849_);
lean_inc_ref(v_e_2842_);
v___x_2868_ = lean_infer_type(v_e_2842_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = l_Lean_Meta_isProp(v_a_2869_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___f_2872_; lean_object* v___x_2873_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___f_2872_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2872_, 0, v_e_2842_);
lean_closure_set(v___f_2872_, 1, v_t_x3f_2841_);
lean_closure_set(v___f_2872_, 2, v_a_2871_);
lean_closure_set(v___f_2872_, 3, v_h_x3f_2840_);
v___x_2873_ = l_Lean_Meta_withExposedNames___redArg(v___f_2872_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
if (lean_obj_tag(v_checkState_x3f_2844_) == 1)
{
lean_object* v_fst_2875_; lean_object* v_snd_2876_; lean_object* v_val_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_fst_2875_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_fst_2875_);
v_snd_2876_ = lean_ctor_get(v_a_2874_, 1);
lean_inc_n(v_snd_2876_, 2);
lean_dec(v_a_2874_);
v_val_2877_ = lean_ctor_get(v_checkState_x3f_2844_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v_checkState_x3f_2844_, 1);
v___x_2878_ = lean_box(0);
v___x_2879_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_2875_, v_snd_2876_, v_val_2877_, v___x_2878_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
if (lean_obj_tag(v_a_2880_) == 1)
{
lean_object* v_val_2881_; lean_object* v_fst_2882_; lean_object* v_snd_2883_; 
lean_dec(v_snd_2876_);
v_val_2881_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_a_2880_, 1);
v_fst_2882_ = lean_ctor_get(v_val_2881_, 0);
lean_inc(v_fst_2882_);
v_snd_2883_ = lean_ctor_get(v_val_2881_, 1);
lean_inc(v_snd_2883_);
lean_dec(v_val_2881_);
v_tac_2855_ = v_fst_2882_;
v_msg_2856_ = v_snd_2883_;
v___y_2857_ = v_a_2851_;
v___y_2858_ = v_a_2852_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_a_2880_);
lean_dec(v_origSpan_x3f_2843_);
lean_dec(v_ref_2839_);
v___x_2884_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
v___x_2885_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_2884_, v_snd_2876_);
v___x_2886_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_2885_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2894_; 
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2895_);
v___x_2888_ = v___x_2886_;
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v___x_2886_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2894_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = lean_box(0);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
return v___x_2886_;
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_snd_2876_);
lean_dec(v_origSpan_x3f_2843_);
lean_dec(v_ref_2839_);
v_a_2896_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2879_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2879_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_fst_2904_; lean_object* v_snd_2905_; 
lean_dec(v_checkState_x3f_2844_);
v_fst_2904_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_fst_2904_);
v_snd_2905_ = lean_ctor_get(v_a_2874_, 1);
lean_inc(v_snd_2905_);
lean_dec(v_a_2874_);
v_tac_2855_ = v_fst_2904_;
v_msg_2856_ = v_snd_2905_;
v___y_2857_ = v_a_2851_;
v___y_2858_ = v_a_2852_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_checkState_x3f_2844_);
lean_dec(v_origSpan_x3f_2843_);
lean_dec(v_ref_2839_);
v_a_2906_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2873_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2873_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_checkState_x3f_2844_);
lean_dec(v_origSpan_x3f_2843_);
lean_dec_ref(v_e_2842_);
lean_dec(v_t_x3f_2841_);
lean_dec(v_h_x3f_2840_);
lean_dec(v_ref_2839_);
v_a_2914_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2870_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2870_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_checkState_x3f_2844_);
lean_dec(v_origSpan_x3f_2843_);
lean_dec_ref(v_e_2842_);
lean_dec(v_t_x3f_2841_);
lean_dec(v_h_x3f_2840_);
lean_dec(v_ref_2839_);
v_a_2922_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2868_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2868_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
v___jp_2854_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
v___x_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v_tac_2855_);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2862_, 0, v_msg_2856_);
v___x_2863_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2860_);
lean_ctor_set(v___x_2863_, 1, v___x_2861_);
lean_ctor_set(v___x_2863_, 2, v___x_2861_);
lean_ctor_set(v___x_2863_, 3, v___x_2861_);
lean_ctor_set(v___x_2863_, 4, v___x_2862_);
lean_ctor_set(v___x_2863_, 5, v___x_2861_);
v___x_2864_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_2865_ = 4;
v___x_2866_ = l_Lean_MessageData_nil;
v___x_2867_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2839_, v___x_2863_, v_origSpan_x3f_2843_, v___x_2864_, v___x_2861_, v___x_2865_, v___x_2866_, v___y_2857_, v___y_2858_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object* v_ref_2930_, lean_object* v_h_x3f_2931_, lean_object* v_t_x3f_2932_, lean_object* v_e_2933_, lean_object* v_origSpan_x3f_2934_, lean_object* v_checkState_x3f_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(v_ref_2930_, v_h_x3f_2931_, v_t_x3f_2932_, v_e_2933_, v_origSpan_x3f_2934_, v_checkState_x3f_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
if (lean_obj_tag(v_a_2947_) == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = l_List_reverse___redArg(v_a_2948_);
return v___x_2949_;
}
else
{
lean_object* v_head_2950_; lean_object* v_tail_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2983_; 
v_head_2950_ = lean_ctor_get(v_a_2947_, 0);
v_tail_2951_ = lean_ctor_get(v_a_2947_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2953_ = v_a_2947_;
v_isShared_2954_ = v_isSharedCheck_2983_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_tail_2951_);
lean_inc(v_head_2950_);
lean_dec(v_a_2947_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2983_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___y_2956_; lean_object* v_fst_2961_; lean_object* v_snd_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2982_; 
v_fst_2961_ = lean_ctor_get(v_head_2950_, 0);
v_snd_2962_ = lean_ctor_get(v_head_2950_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_head_2950_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2964_ = v_head_2950_;
v_isShared_2965_ = v_isSharedCheck_2982_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_snd_2962_);
lean_inc(v_fst_2961_);
lean_dec(v_head_2950_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2982_;
goto v_resetjp_2963_;
}
v___jp_2955_:
{
lean_object* v___x_2958_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v_a_2948_);
lean_ctor_set(v___x_2953_, 0, v___y_2956_);
v___x_2958_ = v___x_2953_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___y_2956_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_a_2948_);
v___x_2958_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
v_a_2947_ = v_tail_2951_;
v_a_2948_ = v___x_2958_;
goto _start;
}
}
v_resetjp_2963_:
{
lean_object* v___y_2967_; uint8_t v___x_2979_; 
v___x_2979_ = lean_unbox(v_snd_2962_);
lean_dec(v_snd_2962_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
v___x_2980_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_2967_ = v___x_2980_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_2981_; 
v___x_2981_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0));
v___y_2967_ = v___x_2981_;
goto v___jp_2966_;
}
v___jp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
lean_inc_ref(v___y_2967_);
v___x_2968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___y_2967_);
v___x_2969_ = l_Lean_MessageData_ofFormat(v___x_2968_);
v___x_2970_ = l_Lean_Expr_isConst(v_fst_2961_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = l_Lean_MessageData_ofExpr(v_fst_2961_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set_tag(v___x_2964_, 7);
lean_ctor_set(v___x_2964_, 1, v___x_2971_);
lean_ctor_set(v___x_2964_, 0, v___x_2969_);
v___x_2973_ = v___x_2964_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
v___y_2956_ = v___x_2973_;
goto v___jp_2955_;
}
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2975_ = l_Lean_MessageData_ofConst(v_fst_2961_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set_tag(v___x_2964_, 7);
lean_ctor_set(v___x_2964_, 1, v___x_2975_);
lean_ctor_set(v___x_2964_, 0, v___x_2969_);
v___x_2977_ = v___x_2964_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v___y_2956_ = v___x_2977_;
goto v___jp_2955_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t v_sz_2991_, size_t v_i_2992_, lean_object* v_bs_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_usize_dec_lt(v_i_2992_, v_sz_2991_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_bs_2993_);
return v___x_3000_;
}
else
{
lean_object* v_v_3001_; lean_object* v_fst_3002_; lean_object* v_snd_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3047_; 
v_v_3001_ = lean_array_uget(v_bs_2993_, v_i_2992_);
v_fst_3002_ = lean_ctor_get(v_v_3001_, 0);
v_snd_3003_ = lean_ctor_get(v_v_3001_, 1);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_v_3001_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3005_ = v_v_3001_;
v_isShared_3006_ = v_isSharedCheck_3047_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_snd_3003_);
lean_inc(v_fst_3002_);
lean_dec(v_v_3001_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3047_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v_bs_x27_3008_; lean_object* v_a_3010_; lean_object* v___x_3015_; 
v___x_3007_ = lean_unsigned_to_nat(0u);
v_bs_x27_3008_ = lean_array_uset(v_bs_2993_, v_i_2992_, v___x_3007_);
v___x_3015_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_fst_3002_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3015_) == 0)
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_unbox(v_snd_3003_);
if (v___x_3016_ == 0)
{
lean_object* v_a_3017_; lean_object* v_ref_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_3005_);
v_a_3017_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3015_, 1);
v_ref_3018_ = lean_ctor_get(v___y_2996_, 5);
v___x_3019_ = lean_unbox(v_snd_3003_);
lean_dec(v_snd_3003_);
v___x_3020_ = l_Lean_SourceInfo_fromRef(v_ref_3018_, v___x_3019_);
v___x_3021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3023_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
lean_inc(v___x_3020_);
v___x_3024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3020_);
lean_ctor_set(v___x_3024_, 1, v___x_3022_);
lean_ctor_set(v___x_3024_, 2, v___x_3023_);
v___x_3025_ = l_Lean_Syntax_node2(v___x_3020_, v___x_3021_, v___x_3024_, v_a_3017_);
v_a_3010_ = v___x_3025_;
goto v___jp_3009_;
}
else
{
lean_object* v_a_3026_; lean_object* v_ref_3027_; uint8_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_dec(v_snd_3003_);
v_a_3026_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3015_, 1);
v_ref_3027_ = lean_ctor_get(v___y_2996_, 5);
v___x_3028_ = 0;
v___x_3029_ = l_Lean_SourceInfo_fromRef(v_ref_3027_, v___x_3028_);
v___x_3030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2));
lean_inc(v___x_3029_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 2);
lean_ctor_set(v___x_3005_, 1, v___x_3032_);
lean_ctor_set(v___x_3005_, 0, v___x_3029_);
v___x_3034_ = v___x_3005_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_inc(v___x_3029_);
v___x_3035_ = l_Lean_Syntax_node1(v___x_3029_, v___x_3031_, v___x_3034_);
v___x_3036_ = l_Lean_Syntax_node2(v___x_3029_, v___x_3030_, v___x_3035_, v_a_3026_);
v_a_3010_ = v___x_3036_;
goto v___jp_3009_;
}
}
}
else
{
lean_del_object(v___x_3005_);
lean_dec(v_snd_3003_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3038_; 
v_a_3038_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3015_, 1);
v_a_3010_ = v_a_3038_;
goto v___jp_3009_;
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_bs_x27_3008_);
v_a_3039_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3015_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3015_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
v___jp_3009_:
{
size_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((size_t)1ULL);
v___x_3012_ = lean_usize_add(v_i_2992_, v___x_3011_);
v___x_3013_ = lean_array_uset(v_bs_x27_3008_, v_i_2992_, v_a_3010_);
v_i_2992_ = v___x_3012_;
v_bs_2993_ = v___x_3013_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object* v_sz_3048_, lean_object* v_i_3049_, lean_object* v_bs_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
size_t v_sz_boxed_3056_; size_t v_i_boxed_3057_; lean_object* v_res_3058_; 
v_sz_boxed_3056_ = lean_unbox_usize(v_sz_3048_);
lean_dec(v_sz_3048_);
v_i_boxed_3057_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_res_3058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_boxed_3056_, v_i_boxed_3057_, v_bs_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
return v_res_3058_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2));
v___x_3064_ = l_Lean_stringToMessageData(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6));
v___x_3071_ = l_Lean_MessageData_ofFormat(v___x_3070_);
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8));
v___x_3074_ = l_Lean_stringToMessageData(v___x_3073_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10));
v___x_3077_ = l_Lean_stringToMessageData(v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object* v___x_3115_, lean_object* v_type_x3f_3116_, lean_object* v_rules_3117_, lean_object* v_loc_x3f_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v_extraMsg_3127_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; size_t v_sz_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v_sz_3172_ = lean_array_size(v___x_3115_);
v___x_3173_ = ((size_t)0ULL);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_3172_, v___x_3173_, v___x_3115_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v_a_3179_; lean_object* v_a_3204_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v___x_3176_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12));
v___x_3177_ = l_Lean_Syntax_SepArray_ofElems(v___x_3176_, v_a_3175_);
lean_dec(v_a_3175_);
if (lean_obj_tag(v_loc_x3f_3118_) == 0)
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_box(0);
v_a_3179_ = v___x_3206_;
goto v___jp_3178_;
}
else
{
lean_object* v_val_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_val_3207_ = lean_ctor_get(v_loc_x3f_3118_, 0);
v___x_3208_ = lean_box(1);
lean_inc(v_val_3207_);
v___x_3209_ = l_Lean_PrettyPrinter_delab(v_val_3207_, v___x_3208_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v_ref_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v_ref_3211_ = lean_ctor_get(v___y_3121_, 5);
v___x_3212_ = 0;
v___x_3213_ = l_Lean_SourceInfo_fromRef(v_ref_3211_, v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24));
v___x_3215_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25));
lean_inc_n(v___x_3213_, 3);
v___x_3216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3213_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27));
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3219_ = l_Lean_Syntax_node1(v___x_3213_, v___x_3218_, v_a_3210_);
v___x_3220_ = l_Lean_Syntax_node1(v___x_3213_, v___x_3217_, v___x_3219_);
v___x_3221_ = l_Lean_Syntax_node2(v___x_3213_, v___x_3214_, v___x_3216_, v___x_3220_);
v_a_3204_ = v___x_3221_;
goto v___jp_3203_;
}
else
{
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3222_; 
v_a_3222_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3209_, 1);
v_a_3204_ = v_a_3222_;
goto v___jp_3203_;
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref_known(v_loc_x3f_3118_, 1);
lean_dec_ref(v___x_3177_);
lean_dec(v_rules_3117_);
lean_dec(v_type_x3f_3116_);
v_a_3223_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3209_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3209_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
v___jp_3178_:
{
lean_object* v_ref_3180_; uint8_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_ref_3180_ = lean_ctor_get(v___y_3121_, 5);
v___x_3181_ = 0;
v___x_3182_ = l_Lean_SourceInfo_fromRef(v_ref_3180_, v___x_3181_);
v___x_3183_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14));
v___x_3184_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15));
lean_inc_n(v___x_3182_, 7);
v___x_3185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3182_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17));
v___x_3187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3188_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_3189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3182_);
lean_ctor_set(v___x_3189_, 1, v___x_3187_);
lean_ctor_set(v___x_3189_, 2, v___x_3188_);
v___x_3190_ = l_Lean_Syntax_node1(v___x_3182_, v___x_3186_, v___x_3189_);
v___x_3191_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19));
v___x_3192_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20));
v___x_3193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3182_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = l_Array_append___redArg(v___x_3188_, v___x_3177_);
lean_dec_ref(v___x_3177_);
v___x_3195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3182_);
lean_ctor_set(v___x_3195_, 1, v___x_3187_);
lean_ctor_set(v___x_3195_, 2, v___x_3194_);
v___x_3196_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21));
v___x_3197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3182_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = l_Lean_Syntax_node3(v___x_3182_, v___x_3191_, v___x_3193_, v___x_3195_, v___x_3197_);
if (lean_obj_tag(v_a_3179_) == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___y_3147_ = v___x_3187_;
v___y_3148_ = v___x_3190_;
v___y_3149_ = v___x_3198_;
v___y_3150_ = v___x_3188_;
v___y_3151_ = v___x_3185_;
v___y_3152_ = v___x_3182_;
v___y_3153_ = v___x_3183_;
v___y_3154_ = v___x_3199_;
goto v___jp_3146_;
}
else
{
lean_object* v_val_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_val_3200_ = lean_ctor_get(v_a_3179_, 0);
lean_inc(v_val_3200_);
lean_dec_ref_known(v_a_3179_, 1);
v___x_3201_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___x_3202_ = lean_array_push(v___x_3201_, v_val_3200_);
v___y_3147_ = v___x_3187_;
v___y_3148_ = v___x_3190_;
v___y_3149_ = v___x_3198_;
v___y_3150_ = v___x_3188_;
v___y_3151_ = v___x_3185_;
v___y_3152_ = v___x_3182_;
v___y_3153_ = v___x_3183_;
v___y_3154_ = v___x_3202_;
goto v___jp_3146_;
}
}
v___jp_3203_:
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_a_3204_);
v_a_3179_ = v___x_3205_;
goto v___jp_3178_;
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v_loc_x3f_3118_);
lean_dec(v_rules_3117_);
lean_dec(v_type_x3f_3116_);
v_a_3231_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3174_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3174_);
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
v___jp_3124_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___y_3125_);
lean_ctor_set(v___x_3128_, 1, v_extraMsg_3127_);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___y_3126_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
v___jp_3131_:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___y_3133_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
switch(lean_obj_tag(v_type_x3f_3116_))
{
case 0:
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v___x_3136_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1);
v___y_3125_ = v_a_3135_;
v___y_3126_ = v___y_3132_;
v_extraMsg_3127_ = v___x_3136_;
goto v___jp_3124_;
}
case 1:
{
lean_object* v_a_3137_; lean_object* v_a_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v_a_3143_; 
v_a_3137_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3134_);
v_a_3138_ = lean_ctor_get(v_type_x3f_3116_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v_type_x3f_3116_, 1);
v___x_3139_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3);
v___x_3140_ = l_Lean_MessageData_ofExpr(v_a_3138_);
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_3141_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref(v___x_3142_);
v___y_3125_ = v_a_3137_;
v___y_3126_ = v___y_3132_;
v_extraMsg_3127_ = v_a_3143_;
goto v___jp_3124_;
}
default: 
{
lean_object* v_a_3144_; lean_object* v___x_3145_; 
v_a_3144_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3134_);
v___x_3145_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4);
v___y_3125_ = v_a_3144_;
v___y_3126_ = v___y_3132_;
v_extraMsg_3127_ = v___x_3145_;
goto v___jp_3124_;
}
}
}
v___jp_3146_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3155_ = l_Array_append___redArg(v___y_3150_, v___y_3154_);
lean_dec_ref(v___y_3154_);
lean_inc(v___y_3147_);
lean_inc(v___y_3152_);
v___x_3156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3156_, 0, v___y_3152_);
lean_ctor_set(v___x_3156_, 1, v___y_3147_);
lean_ctor_set(v___x_3156_, 2, v___x_3155_);
lean_inc(v___y_3153_);
v___x_3157_ = l_Lean_Syntax_node4(v___y_3152_, v___y_3153_, v___y_3151_, v___y_3148_, v___y_3149_, v___x_3156_);
v___x_3158_ = lean_box(0);
v___x_3159_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(v_rules_3117_, v___x_3158_);
v___x_3160_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7);
v___x_3161_ = l_Lean_MessageData_joinSep(v___x_3159_, v___x_3160_);
v___x_3162_ = l_Lean_MessageData_sbracket(v___x_3161_);
if (lean_obj_tag(v_loc_x3f_3118_) == 1)
{
lean_object* v_val_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_val_3163_ = lean_ctor_get(v_loc_x3f_3118_, 0);
lean_inc(v_val_3163_);
lean_dec_ref_known(v_loc_x3f_3118_, 1);
v___x_3164_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___x_3162_);
v___x_3166_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = l_Lean_MessageData_ofExpr(v_val_3163_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___y_3132_ = v___x_3157_;
v___y_3133_ = v___x_3169_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v_loc_x3f_3118_);
v___x_3170_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3162_);
v___y_3132_ = v___x_3157_;
v___y_3133_ = v___x_3171_;
goto v___jp_3131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(lean_object* v___x_3239_, lean_object* v_type_x3f_3240_, lean_object* v_rules_3241_, lean_object* v_loc_x3f_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(v___x_3239_, v_type_x3f_3240_, v_rules_3241_, v_loc_x3f_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3248_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1));
v___x_3253_ = l_Lean_MessageData_ofFormat(v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* v_ref_3254_, lean_object* v_rules_3255_, lean_object* v_type_x3f_3256_, lean_object* v_loc_x3f_3257_, lean_object* v_origSpan_x3f_3258_, lean_object* v_checkState_x3f_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; lean_object* v___f_3270_; lean_object* v___x_3271_; 
lean_inc(v_rules_3255_);
v___x_3269_ = lean_array_mk(v_rules_3255_);
lean_inc(v_type_x3f_3256_);
v___f_3270_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3270_, 0, v___x_3269_);
lean_closure_set(v___f_3270_, 1, v_type_x3f_3256_);
lean_closure_set(v___f_3270_, 2, v_rules_3255_);
lean_closure_set(v___f_3270_, 3, v_loc_x3f_3257_);
v___x_3271_ = l_Lean_Meta_withExposedNames___redArg(v___f_3270_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v_snd_3273_; lean_object* v_fst_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3345_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v_snd_3273_ = lean_ctor_get(v_a_3272_, 1);
v_fst_3274_ = lean_ctor_get(v_a_3272_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_a_3272_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3276_ = v_a_3272_;
v_isShared_3277_ = v_isSharedCheck_3345_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_snd_3273_);
lean_inc(v_fst_3274_);
lean_dec(v_a_3272_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3345_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v_fst_3278_; lean_object* v_snd_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3344_; 
v_fst_3278_ = lean_ctor_get(v_snd_3273_, 0);
v_snd_3279_ = lean_ctor_get(v_snd_3273_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_snd_3273_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3281_ = v_snd_3273_;
v_isShared_3282_ = v_isSharedCheck_3344_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_snd_3279_);
lean_inc(v_fst_3278_);
lean_dec(v_snd_3273_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3344_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_tac_3284_; lean_object* v_tacMsg_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; 
if (lean_obj_tag(v_checkState_x3f_3259_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3343_; 
v_val_3302_ = lean_ctor_get(v_checkState_x3f_3259_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_checkState_x3f_3259_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3304_ = v_checkState_x3f_3259_;
v_isShared_3305_ = v_isSharedCheck_3343_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_val_3302_);
lean_dec(v_checkState_x3f_3259_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3343_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___y_3307_; 
if (lean_obj_tag(v_type_x3f_3256_) == 1)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; 
v_a_3338_ = lean_ctor_get(v_type_x3f_3256_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v_type_x3f_3256_, 1);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v_a_3338_);
v___x_3340_ = v___x_3304_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
v___y_3307_ = v___x_3340_;
goto v___jp_3306_;
}
}
else
{
lean_object* v___x_3342_; 
lean_del_object(v___x_3304_);
lean_dec(v_type_x3f_3256_);
v___x_3342_ = lean_box(0);
v___y_3307_ = v___x_3342_;
goto v___jp_3306_;
}
v___jp_3306_:
{
lean_object* v___x_3308_; 
lean_inc(v_fst_3278_);
v___x_3308_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_3274_, v_fst_3278_, v_val_3302_, v___y_3307_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
if (lean_obj_tag(v_a_3309_) == 1)
{
lean_object* v_val_3310_; lean_object* v_fst_3311_; lean_object* v_snd_3312_; 
lean_dec(v_fst_3278_);
v_val_3310_ = lean_ctor_get(v_a_3309_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v_a_3309_, 1);
v_fst_3311_ = lean_ctor_get(v_val_3310_, 0);
lean_inc(v_fst_3311_);
v_snd_3312_ = lean_ctor_get(v_val_3310_, 1);
lean_inc(v_snd_3312_);
lean_dec(v_val_3310_);
v_tac_3284_ = v_fst_3311_;
v_tacMsg_3285_ = v_snd_3312_;
v___y_3286_ = v_a_3266_;
v___y_3287_ = v_a_3267_;
goto v___jp_3283_;
}
else
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec(v_a_3309_);
lean_del_object(v___x_3281_);
lean_del_object(v___x_3276_);
lean_dec(v_origSpan_x3f_3258_);
lean_dec(v_ref_3254_);
v___x_3313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v_fst_3278_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v_snd_3279_);
v___x_3319_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_3317_, v___x_3318_);
v___x_3320_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_3319_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3328_; 
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v___x_3320_, 0);
lean_dec(v_unused_3329_);
v___x_3322_ = v___x_3320_;
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v___x_3320_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3324_ = lean_box(0);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3324_);
v___x_3326_ = v___x_3322_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
else
{
return v___x_3320_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_del_object(v___x_3281_);
lean_dec(v_snd_3279_);
lean_dec(v_fst_3278_);
lean_del_object(v___x_3276_);
lean_dec(v_origSpan_x3f_3258_);
lean_dec(v_ref_3254_);
v_a_3330_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3308_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3308_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
else
{
lean_dec(v_checkState_x3f_3259_);
lean_dec(v_type_x3f_3256_);
v_tac_3284_ = v_fst_3274_;
v_tacMsg_3285_ = v_fst_3278_;
v___y_3286_ = v_a_3266_;
v___y_3287_ = v_a_3267_;
goto v___jp_3283_;
}
v___jp_3283_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v_tac_3284_);
lean_ctor_set(v___x_3281_, 0, v___x_3288_);
v___x_3290_ = v___x_3281_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_tac_3284_);
v___x_3290_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_box(0);
if (v_isShared_3277_ == 0)
{
lean_ctor_set_tag(v___x_3276_, 7);
lean_ctor_set(v___x_3276_, 1, v_snd_3279_);
lean_ctor_set(v___x_3276_, 0, v_tacMsg_3285_);
v___x_3293_ = v___x_3276_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_tacMsg_3285_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_snd_3279_);
v___x_3293_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3290_);
lean_ctor_set(v___x_3295_, 1, v___x_3291_);
lean_ctor_set(v___x_3295_, 2, v___x_3291_);
lean_ctor_set(v___x_3295_, 3, v___x_3291_);
lean_ctor_set(v___x_3295_, 4, v___x_3294_);
lean_ctor_set(v___x_3295_, 5, v___x_3291_);
v___x_3296_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_3297_ = 4;
v___x_3298_ = l_Lean_MessageData_nil;
v___x_3299_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3254_, v___x_3295_, v_origSpan_x3f_3258_, v___x_3296_, v___x_3291_, v___x_3297_, v___x_3298_, v___y_3286_, v___y_3287_);
return v___x_3299_;
}
}
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_checkState_x3f_3259_);
lean_dec(v_origSpan_x3f_3258_);
lean_dec(v_type_x3f_3256_);
lean_dec(v_ref_3254_);
v_a_3346_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3271_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3271_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object* v_ref_3354_, lean_object* v_rules_3355_, lean_object* v_type_x3f_3356_, lean_object* v_loc_x3f_3357_, lean_object* v_origSpan_x3f_3358_, lean_object* v_checkState_x3f_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3354_, v_rules_3355_, v_type_x3f_3356_, v_loc_x3f_3357_, v_origSpan_x3f_3358_, v_checkState_x3f_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
return v_res_3369_;
}
}
lean_object* runtime_initialize_Lean_Server_CodeActions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
