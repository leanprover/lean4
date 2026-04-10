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
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_mk_syntax_ident(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3;
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
lean_dec_ref(v___x_47_);
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
lean_dec_ref(v___x_170_);
if (lean_obj_tag(v_val_172_) == 1)
{
uint8_t v_v_173_; 
v_v_173_ = lean_ctor_get_uint8(v_val_172_, 0);
lean_dec_ref(v_val_172_);
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
lean_dec_ref(v___x_184_);
if (lean_obj_tag(v_val_185_) == 3)
{
lean_object* v_v_186_; 
v_v_186_ = lean_ctor_get(v_val_185_, 0);
lean_inc(v_v_186_);
lean_dec_ref(v_val_185_);
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
lean_object* v___x_238_; lean_object* v_fileName_239_; lean_object* v_fileMap_240_; lean_object* v_options_241_; lean_object* v_currRecDepth_242_; lean_object* v_ref_243_; lean_object* v_currNamespace_244_; lean_object* v_openDecls_245_; lean_object* v_initHeartbeats_246_; lean_object* v_maxHeartbeats_247_; lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_cancelTk_x3f_250_; uint8_t v_suppressElabErrors_251_; lean_object* v_inheritedTraceOptions_252_; lean_object* v_env_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v_fileName_261_; lean_object* v_fileMap_262_; lean_object* v_currRecDepth_263_; lean_object* v_ref_264_; lean_object* v_currNamespace_265_; lean_object* v_openDecls_266_; lean_object* v_initHeartbeats_267_; lean_object* v_maxHeartbeats_268_; lean_object* v_quotContext_269_; lean_object* v_currMacroScope_270_; lean_object* v_cancelTk_x3f_271_; uint8_t v_suppressElabErrors_272_; lean_object* v_inheritedTraceOptions_273_; lean_object* v___y_274_; uint8_t v___y_280_; uint8_t v___x_301_; 
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
v___x_301_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_253_);
lean_dec_ref(v_env_253_);
if (v___x_301_ == 0)
{
if (v___x_259_ == 0)
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
v___y_280_ = v___x_301_;
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
lean_dec_ref(v___x_277_);
return v___x_278_;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
lean_object* v___x_281_; lean_object* v_env_282_; lean_object* v_nextMacroScope_283_; lean_object* v_ngen_284_; lean_object* v_auxDeclNGen_285_; lean_object* v_traceState_286_; lean_object* v_messages_287_; lean_object* v_infoState_288_; lean_object* v_snapshotTasks_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
v___x_281_ = lean_st_ref_take(v_a_236_);
v_env_282_ = lean_ctor_get(v___x_281_, 0);
v_nextMacroScope_283_ = lean_ctor_get(v___x_281_, 1);
v_ngen_284_ = lean_ctor_get(v___x_281_, 2);
v_auxDeclNGen_285_ = lean_ctor_get(v___x_281_, 3);
v_traceState_286_ = lean_ctor_get(v___x_281_, 4);
v_messages_287_ = lean_ctor_get(v___x_281_, 6);
v_infoState_288_ = lean_ctor_get(v___x_281_, 7);
v_snapshotTasks_289_ = lean_ctor_get(v___x_281_, 8);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v___x_281_, 5);
lean_dec(v_unused_300_);
v___x_291_ = v___x_281_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snapshotTasks_289_);
lean_inc(v_infoState_288_);
lean_inc(v_messages_287_);
lean_inc(v_traceState_286_);
lean_inc(v_auxDeclNGen_285_);
lean_inc(v_ngen_284_);
lean_inc(v_nextMacroScope_283_);
lean_inc(v_env_282_);
lean_dec(v___x_281_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = l_Lean_Kernel_enableDiag(v_env_282_, v___x_259_);
v___x_294_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 5, v___x_294_);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_nextMacroScope_283_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_ngen_284_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_auxDeclNGen_285_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_traceState_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 5, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_298_, 6, v_messages_287_);
lean_ctor_set(v_reuseFailAlloc_298_, 7, v_infoState_288_);
lean_ctor_set(v_reuseFailAlloc_298_, 8, v_snapshotTasks_289_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_st_ref_set(v_a_236_, v___x_296_);
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
else
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___boxed(lean_object* v_e_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(lean_object* v_msgData_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v_mctx_318_; lean_object* v_lctx_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_315_ = lean_st_ref_get(v___y_313_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_env_316_);
lean_dec(v___x_315_);
v___x_317_ = lean_st_ref_get(v___y_311_);
v_mctx_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_mctx_318_);
lean_dec(v___x_317_);
v_lctx_319_ = lean_ctor_get(v___y_310_, 2);
v_options_320_ = lean_ctor_get(v___y_312_, 2);
lean_inc_ref(v_options_320_);
lean_inc_ref(v_lctx_319_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_316_);
lean_ctor_set(v___x_321_, 1, v_mctx_318_);
lean_ctor_set(v___x_321_, 2, v_lctx_319_);
lean_ctor_set(v___x_321_, 3, v_options_320_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_309_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
lean_inc_ref(v_e_334_);
v___x_340_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_356_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
v___x_342_ = l_Lean_MessageData_ofExpr(v_e_334_);
v___x_343_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_342_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_356_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_356_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_356_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_348_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1));
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_341_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_a_344_);
v___x_352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_352_, 0, v___x_349_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
lean_ctor_set(v___x_352_, 2, v___x_350_);
lean_ctor_set(v___x_352_, 3, v___x_350_);
lean_ctor_set(v___x_352_, 4, v___x_351_);
lean_ctor_set(v___x_352_, 5, v___x_350_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_352_);
v___x_354_ = v___x_346_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v_e_334_);
v_a_357_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_340_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_340_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___boxed(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_372_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
lean_ctor_set(v___x_377_, 2, v___x_376_);
lean_ctor_set(v___x_377_, 3, v___x_376_);
lean_ctor_set(v___x_377_, 4, v___x_375_);
lean_ctor_set(v___x_377_, 5, v___x_375_);
lean_ctor_set(v___x_377_, 6, v___x_375_);
lean_ctor_set(v___x_377_, 7, v___x_375_);
lean_ctor_set(v___x_377_, 8, v___x_375_);
lean_ctor_set(v___x_377_, 9, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_unsigned_to_nat(32u);
v___x_379_ = lean_mk_empty_array_with_capacity(v___x_378_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_381_ = ((size_t)5ULL);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_unsigned_to_nat(32u);
v___x_384_ = lean_mk_empty_array_with_capacity(v___x_383_);
v___x_385_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__3);
v___x_386_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
lean_ctor_set(v___x_386_, 2, v___x_382_);
lean_ctor_set(v___x_386_, 3, v___x_382_);
lean_ctor_set_usize(v___x_386_, 4, v___x_381_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_box(1);
v___x_388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__4);
v___x_389_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__1);
v___x_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(lean_object* v_msgData_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v_options_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_395_ = lean_st_ref_get(v___y_393_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
v_options_397_ = lean_ctor_get(v___y_392_, 2);
v___x_398_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__2);
v___x_399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_397_);
v___x_400_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_400_, 0, v_env_396_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
lean_ctor_set(v___x_400_, 2, v___x_399_);
lean_ctor_set(v___x_400_, 3, v_options_397_);
v___x_401_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v_msgData_391_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msgData_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_407_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(uint8_t v___y_414_, uint8_t v_suppressElabErrors_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 1)
{
lean_object* v_pre_417_; 
v_pre_417_ = lean_ctor_get(v_x_416_, 0);
switch(lean_obj_tag(v_pre_417_))
{
case 1:
{
lean_object* v_pre_418_; 
v_pre_418_ = lean_ctor_get(v_pre_417_, 0);
switch(lean_obj_tag(v_pre_418_))
{
case 0:
{
lean_object* v_str_419_; lean_object* v_str_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_str_419_ = lean_ctor_get(v_x_416_, 1);
v_str_420_ = lean_ctor_get(v_pre_417_, 1);
v___x_421_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__0));
v___x_422_ = lean_string_dec_eq(v_str_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__4));
v___x_424_ = lean_string_dec_eq(v_str_420_, v___x_423_);
if (v___x_424_ == 0)
{
return v___y_414_;
}
else
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__1));
v___x_426_ = lean_string_dec_eq(v_str_419_, v___x_425_);
if (v___x_426_ == 0)
{
return v___y_414_;
}
else
{
return v_suppressElabErrors_415_;
}
}
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__2));
v___x_428_ = lean_string_dec_eq(v_str_419_, v___x_427_);
if (v___x_428_ == 0)
{
return v___y_414_;
}
else
{
return v_suppressElabErrors_415_;
}
}
}
case 1:
{
lean_object* v_pre_429_; 
v_pre_429_ = lean_ctor_get(v_pre_418_, 0);
if (lean_obj_tag(v_pre_429_) == 0)
{
lean_object* v_str_430_; lean_object* v_str_431_; lean_object* v_str_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_str_430_ = lean_ctor_get(v_x_416_, 1);
v_str_431_ = lean_ctor_get(v_pre_417_, 1);
v_str_432_ = lean_ctor_get(v_pre_418_, 1);
v___x_433_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__3));
v___x_434_ = lean_string_dec_eq(v_str_432_, v___x_433_);
if (v___x_434_ == 0)
{
return v___y_414_;
}
else
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__4));
v___x_436_ = lean_string_dec_eq(v_str_431_, v___x_435_);
if (v___x_436_ == 0)
{
return v___y_414_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___closed__5));
v___x_438_ = lean_string_dec_eq(v_str_430_, v___x_437_);
if (v___x_438_ == 0)
{
return v___y_414_;
}
else
{
return v_suppressElabErrors_415_;
}
}
}
}
else
{
return v___y_414_;
}
}
default: 
{
return v___y_414_;
}
}
}
case 0:
{
lean_object* v_str_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_str_439_ = lean_ctor_get(v_x_416_, 1);
v___x_440_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0_spec__0___closed__0));
v___x_441_ = lean_string_dec_eq(v_str_439_, v___x_440_);
if (v___x_441_ == 0)
{
return v___y_414_;
}
else
{
return v_suppressElabErrors_415_;
}
}
default: 
{
return v___y_414_;
}
}
}
else
{
return v___y_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed(lean_object* v___y_442_, lean_object* v_suppressElabErrors_443_, lean_object* v_x_444_){
_start:
{
uint8_t v___y_2399__boxed_445_; uint8_t v_suppressElabErrors_boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v___y_2399__boxed_445_ = lean_unbox(v___y_442_);
v_suppressElabErrors_boxed_446_ = lean_unbox(v_suppressElabErrors_443_);
v_res_447_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v___y_2399__boxed_445_, v_suppressElabErrors_boxed_446_, v_x_444_);
lean_dec(v_x_444_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(lean_object* v_ref_450_, lean_object* v_msgData_451_, uint8_t v_severity_452_, uint8_t v_isSilent_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; uint8_t v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_494_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; uint8_t v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; uint8_t v___y_534_; lean_object* v___y_535_; uint8_t v___y_536_; uint8_t v___x_541_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___y_551_; uint8_t v___x_566_; 
v___x_541_ = 2;
v___x_566_ = l_Lean_instBEqMessageSeverity_beq(v_severity_452_, v___x_541_);
if (v___x_566_ == 0)
{
v___y_551_ = v___x_566_;
goto v___jp_550_;
}
else
{
uint8_t v___x_567_; 
lean_inc_ref(v_msgData_451_);
v___x_567_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_451_);
v___y_551_ = v___x_567_;
goto v___jp_550_;
}
v___jp_457_:
{
lean_object* v___x_467_; lean_object* v_currNamespace_468_; lean_object* v_openDecls_469_; lean_object* v_env_470_; lean_object* v_nextMacroScope_471_; lean_object* v_ngen_472_; lean_object* v_auxDeclNGen_473_; lean_object* v_traceState_474_; lean_object* v_cache_475_; lean_object* v_messages_476_; lean_object* v_infoState_477_; lean_object* v_snapshotTasks_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
v___x_467_ = lean_st_ref_take(v___y_466_);
v_currNamespace_468_ = lean_ctor_get(v___y_465_, 6);
v_openDecls_469_ = lean_ctor_get(v___y_465_, 7);
v_env_470_ = lean_ctor_get(v___x_467_, 0);
v_nextMacroScope_471_ = lean_ctor_get(v___x_467_, 1);
v_ngen_472_ = lean_ctor_get(v___x_467_, 2);
v_auxDeclNGen_473_ = lean_ctor_get(v___x_467_, 3);
v_traceState_474_ = lean_ctor_get(v___x_467_, 4);
v_cache_475_ = lean_ctor_get(v___x_467_, 5);
v_messages_476_ = lean_ctor_get(v___x_467_, 6);
v_infoState_477_ = lean_ctor_get(v___x_467_, 7);
v_snapshotTasks_478_ = lean_ctor_get(v___x_467_, 8);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_492_ == 0)
{
v___x_480_ = v___x_467_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snapshotTasks_478_);
lean_inc(v_infoState_477_);
lean_inc(v_messages_476_);
lean_inc(v_cache_475_);
lean_inc(v_traceState_474_);
lean_inc(v_auxDeclNGen_473_);
lean_inc(v_ngen_472_);
lean_inc(v_nextMacroScope_471_);
lean_inc(v_env_470_);
lean_dec(v___x_467_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_openDecls_469_);
lean_inc(v_currNamespace_468_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_currNamespace_468_);
lean_ctor_set(v___x_482_, 1, v_openDecls_469_);
v___x_483_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___y_458_);
lean_inc_ref(v___y_464_);
lean_inc_ref(v___y_459_);
v___x_484_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_484_, 0, v___y_459_);
lean_ctor_set(v___x_484_, 1, v___y_461_);
lean_ctor_set(v___x_484_, 2, v___y_460_);
lean_ctor_set(v___x_484_, 3, v___y_464_);
lean_ctor_set(v___x_484_, 4, v___x_483_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5, v___y_462_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5 + 1, v___y_463_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5 + 2, v_isSilent_453_);
v___x_485_ = l_Lean_MessageLog_add(v___x_484_, v_messages_476_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 6, v___x_485_);
v___x_487_ = v___x_480_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_env_470_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_nextMacroScope_471_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_ngen_472_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_auxDeclNGen_473_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_traceState_474_);
lean_ctor_set(v_reuseFailAlloc_491_, 5, v_cache_475_);
lean_ctor_set(v_reuseFailAlloc_491_, 6, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_491_, 7, v_infoState_477_);
lean_ctor_set(v_reuseFailAlloc_491_, 8, v_snapshotTasks_478_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_st_ref_set(v___y_466_, v___x_487_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
v___jp_493_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_517_; 
v___x_502_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_451_);
v___x_503_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v___x_502_, v___y_454_, v___y_455_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_517_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_517_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_517_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_inc_ref_n(v___y_499_, 2);
v___x_508_ = l_Lean_FileMap_toPosition(v___y_499_, v___y_497_);
lean_dec(v___y_497_);
v___x_509_ = l_Lean_FileMap_toPosition(v___y_499_, v___y_501_);
lean_dec(v___y_501_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_496_ == 0)
{
lean_del_object(v___x_506_);
lean_dec_ref(v___y_494_);
v___y_458_ = v_a_504_;
v___y_459_ = v___y_495_;
v___y_460_ = v___x_510_;
v___y_461_ = v___x_508_;
v___y_462_ = v___y_498_;
v___y_463_ = v___y_500_;
v___y_464_ = v___x_511_;
v___y_465_ = v___y_454_;
v___y_466_ = v___y_455_;
goto v___jp_457_;
}
else
{
uint8_t v___x_512_; 
lean_inc(v_a_504_);
v___x_512_ = l_Lean_MessageData_hasTag(v___y_494_, v_a_504_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_dec_ref(v___x_510_);
lean_dec_ref(v___x_508_);
lean_dec(v_a_504_);
v___x_513_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_513_);
v___x_515_ = v___x_506_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_del_object(v___x_506_);
v___y_458_ = v_a_504_;
v___y_459_ = v___y_495_;
v___y_460_ = v___x_510_;
v___y_461_ = v___x_508_;
v___y_462_ = v___y_498_;
v___y_463_ = v___y_500_;
v___y_464_ = v___x_511_;
v___y_465_ = v___y_454_;
v___y_466_ = v___y_455_;
goto v___jp_457_;
}
}
}
}
v___jp_518_:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Syntax_getTailPos_x3f(v___y_522_, v___y_524_);
lean_dec(v___y_522_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_inc(v___y_526_);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_520_;
v___y_496_ = v___y_521_;
v___y_497_ = v___y_526_;
v___y_498_ = v___y_524_;
v___y_499_ = v___y_523_;
v___y_500_ = v___y_525_;
v___y_501_ = v___y_526_;
goto v___jp_493_;
}
else
{
lean_object* v_val_528_; 
v_val_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_528_);
lean_dec_ref(v___x_527_);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_520_;
v___y_496_ = v___y_521_;
v___y_497_ = v___y_526_;
v___y_498_ = v___y_524_;
v___y_499_ = v___y_523_;
v___y_500_ = v___y_525_;
v___y_501_ = v_val_528_;
goto v___jp_493_;
}
}
v___jp_529_:
{
lean_object* v_ref_537_; lean_object* v___x_538_; 
v_ref_537_ = l_Lean_replaceRef(v_ref_450_, v___y_533_);
v___x_538_ = l_Lean_Syntax_getPos_x3f(v_ref_537_, v___y_534_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___y_519_ = v___y_530_;
v___y_520_ = v___y_531_;
v___y_521_ = v___y_532_;
v___y_522_ = v_ref_537_;
v___y_523_ = v___y_535_;
v___y_524_ = v___y_534_;
v___y_525_ = v___y_536_;
v___y_526_ = v___x_539_;
goto v___jp_518_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_540_);
lean_dec_ref(v___x_538_);
v___y_519_ = v___y_530_;
v___y_520_ = v___y_531_;
v___y_521_ = v___y_532_;
v___y_522_ = v_ref_537_;
v___y_523_ = v___y_535_;
v___y_524_ = v___y_534_;
v___y_525_ = v___y_536_;
v___y_526_ = v_val_540_;
goto v___jp_518_;
}
}
v___jp_542_:
{
if (v___y_549_ == 0)
{
v___y_530_ = v___y_546_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_545_;
v___y_533_ = v___y_544_;
v___y_534_ = v___y_548_;
v___y_535_ = v___y_547_;
v___y_536_ = v_severity_452_;
goto v___jp_529_;
}
else
{
v___y_530_ = v___y_546_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_545_;
v___y_533_ = v___y_544_;
v___y_534_ = v___y_548_;
v___y_535_ = v___y_547_;
v___y_536_ = v___x_541_;
goto v___jp_529_;
}
}
v___jp_550_:
{
if (v___y_551_ == 0)
{
lean_object* v_fileName_552_; lean_object* v_fileMap_553_; lean_object* v_options_554_; lean_object* v_ref_555_; uint8_t v_suppressElabErrors_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___f_559_; uint8_t v___x_560_; uint8_t v___x_561_; 
v_fileName_552_ = lean_ctor_get(v___y_454_, 0);
v_fileMap_553_ = lean_ctor_get(v___y_454_, 1);
v_options_554_ = lean_ctor_get(v___y_454_, 2);
v_ref_555_ = lean_ctor_get(v___y_454_, 5);
v_suppressElabErrors_556_ = lean_ctor_get_uint8(v___y_454_, sizeof(void*)*14 + 1);
v___x_557_ = lean_box(v___y_551_);
v___x_558_ = lean_box(v_suppressElabErrors_556_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_559_, 0, v___x_557_);
lean_closure_set(v___f_559_, 1, v___x_558_);
v___x_560_ = 1;
v___x_561_ = l_Lean_instBEqMessageSeverity_beq(v_severity_452_, v___x_560_);
if (v___x_561_ == 0)
{
v___y_543_ = v_fileName_552_;
v___y_544_ = v_ref_555_;
v___y_545_ = v_suppressElabErrors_556_;
v___y_546_ = v___f_559_;
v___y_547_ = v_fileMap_553_;
v___y_548_ = v___y_551_;
v___y_549_ = v___x_561_;
goto v___jp_542_;
}
else
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = l_Lean_warningAsError;
v___x_563_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_554_, v___x_562_);
v___y_543_ = v_fileName_552_;
v___y_544_ = v_ref_555_;
v___y_545_ = v_suppressElabErrors_556_;
v___y_546_ = v___f_559_;
v___y_547_ = v_fileMap_553_;
v___y_548_ = v___y_551_;
v___y_549_ = v___x_563_;
goto v___jp_542_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_msgData_451_);
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___boxed(lean_object* v_ref_568_, lean_object* v_msgData_569_, lean_object* v_severity_570_, lean_object* v_isSilent_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v_severity_boxed_575_; uint8_t v_isSilent_boxed_576_; lean_object* v_res_577_; 
v_severity_boxed_575_ = lean_unbox(v_severity_570_);
v_isSilent_boxed_576_ = lean_unbox(v_isSilent_571_);
v_res_577_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_568_, v_msgData_569_, v_severity_boxed_575_, v_isSilent_boxed_576_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v_ref_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object* v_ref_578_, lean_object* v_msgData_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; 
v___x_583_ = 0;
v___x_584_ = 0;
v___x_585_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(v_ref_578_, v_msgData_579_, v___x_583_, v___x_584_, v___y_580_, v___y_581_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object* v_ref_586_, lean_object* v_msgData_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_586_, v_msgData_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v_ref_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* v_ref_592_, lean_object* v_s_593_, lean_object* v_origSpan_x3f_594_, lean_object* v_header_595_, lean_object* v_codeActionPrefix_x3f_596_, uint8_t v_diffGranularity_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_601_; lean_object* v_hintSuggestion_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; 
v___x_601_ = lean_box(0);
v_hintSuggestion_602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_hintSuggestion_602_, 0, v_s_593_);
lean_ctor_set(v_hintSuggestion_602_, 1, v_origSpan_x3f_594_);
lean_ctor_set(v_hintSuggestion_602_, 2, v___x_601_);
lean_ctor_set_uint8(v_hintSuggestion_602_, sizeof(void*)*3, v_diffGranularity_597_);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_mk_empty_array_with_capacity(v___x_603_);
v___x_605_ = lean_array_push(v___x_604_, v_hintSuggestion_602_);
v___x_606_ = 0;
lean_inc(v_ref_592_);
v___x_607_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v___x_605_, v_ref_592_, v_codeActionPrefix_x3f_596_, v___x_606_, v_a_598_, v_a_599_);
lean_dec_ref(v___x_605_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = l_Lean_stringToMessageData(v_header_595_);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_a_608_);
v___x_611_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_592_, v___x_610_, v_a_598_, v_a_599_);
lean_dec(v_ref_592_);
return v___x_611_;
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_header_595_);
lean_dec(v_ref_592_);
v_a_612_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_607_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_607_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* v_ref_620_, lean_object* v_s_621_, lean_object* v_origSpan_x3f_622_, lean_object* v_header_623_, lean_object* v_codeActionPrefix_x3f_624_, lean_object* v_diffGranularity_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
uint8_t v_diffGranularity_boxed_629_; lean_object* v_res_630_; 
v_diffGranularity_boxed_629_ = lean_unbox(v_diffGranularity_625_);
v_res_630_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_620_, v_s_621_, v_origSpan_x3f_622_, v_header_623_, v_codeActionPrefix_x3f_624_, v_diffGranularity_boxed_629_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_ref_635_; lean_object* v___x_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_ref_635_ = lean_ctor_get(v___y_632_, 5);
v___x_636_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msg_631_, v___y_632_, v___y_633_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_inc(v_ref_635_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_ref_635_);
lean_ctor_set(v___x_641_, 1, v_a_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 1);
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(lean_object* v_msg_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(lean_object* v_ref_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_fileName_656_; lean_object* v_fileMap_657_; lean_object* v_options_658_; lean_object* v_currRecDepth_659_; lean_object* v_maxRecDepth_660_; lean_object* v_ref_661_; lean_object* v_currNamespace_662_; lean_object* v_openDecls_663_; lean_object* v_initHeartbeats_664_; lean_object* v_maxHeartbeats_665_; lean_object* v_quotContext_666_; lean_object* v_currMacroScope_667_; uint8_t v_diag_668_; lean_object* v_cancelTk_x3f_669_; uint8_t v_suppressElabErrors_670_; lean_object* v_inheritedTraceOptions_671_; lean_object* v_ref_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_fileName_656_ = lean_ctor_get(v___y_653_, 0);
v_fileMap_657_ = lean_ctor_get(v___y_653_, 1);
v_options_658_ = lean_ctor_get(v___y_653_, 2);
v_currRecDepth_659_ = lean_ctor_get(v___y_653_, 3);
v_maxRecDepth_660_ = lean_ctor_get(v___y_653_, 4);
v_ref_661_ = lean_ctor_get(v___y_653_, 5);
v_currNamespace_662_ = lean_ctor_get(v___y_653_, 6);
v_openDecls_663_ = lean_ctor_get(v___y_653_, 7);
v_initHeartbeats_664_ = lean_ctor_get(v___y_653_, 8);
v_maxHeartbeats_665_ = lean_ctor_get(v___y_653_, 9);
v_quotContext_666_ = lean_ctor_get(v___y_653_, 10);
v_currMacroScope_667_ = lean_ctor_get(v___y_653_, 11);
v_diag_668_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*14);
v_cancelTk_x3f_669_ = lean_ctor_get(v___y_653_, 12);
v_suppressElabErrors_670_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_671_ = lean_ctor_get(v___y_653_, 13);
v_ref_672_ = l_Lean_replaceRef(v_ref_651_, v_ref_661_);
lean_inc_ref(v_inheritedTraceOptions_671_);
lean_inc(v_cancelTk_x3f_669_);
lean_inc(v_currMacroScope_667_);
lean_inc(v_quotContext_666_);
lean_inc(v_maxHeartbeats_665_);
lean_inc(v_initHeartbeats_664_);
lean_inc(v_openDecls_663_);
lean_inc(v_currNamespace_662_);
lean_inc(v_maxRecDepth_660_);
lean_inc(v_currRecDepth_659_);
lean_inc_ref(v_options_658_);
lean_inc_ref(v_fileMap_657_);
lean_inc_ref(v_fileName_656_);
v___x_673_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_673_, 0, v_fileName_656_);
lean_ctor_set(v___x_673_, 1, v_fileMap_657_);
lean_ctor_set(v___x_673_, 2, v_options_658_);
lean_ctor_set(v___x_673_, 3, v_currRecDepth_659_);
lean_ctor_set(v___x_673_, 4, v_maxRecDepth_660_);
lean_ctor_set(v___x_673_, 5, v_ref_672_);
lean_ctor_set(v___x_673_, 6, v_currNamespace_662_);
lean_ctor_set(v___x_673_, 7, v_openDecls_663_);
lean_ctor_set(v___x_673_, 8, v_initHeartbeats_664_);
lean_ctor_set(v___x_673_, 9, v_maxHeartbeats_665_);
lean_ctor_set(v___x_673_, 10, v_quotContext_666_);
lean_ctor_set(v___x_673_, 11, v_currMacroScope_667_);
lean_ctor_set(v___x_673_, 12, v_cancelTk_x3f_669_);
lean_ctor_set(v___x_673_, 13, v_inheritedTraceOptions_671_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*14, v_diag_668_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*14 + 1, v_suppressElabErrors_670_);
v___x_674_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_652_, v___x_673_, v___y_654_);
lean_dec_ref(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg___boxed(lean_object* v_ref_675_, lean_object* v_msg_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_675_, v_msg_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v_ref_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(lean_object* v_origSpan_x3f_681_, uint8_t v_diffGranularity_682_, size_t v_sz_683_, size_t v_i_684_, lean_object* v_bs_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_686_ == 0)
{
lean_dec(v_origSpan_x3f_681_);
return v_bs_685_;
}
else
{
lean_object* v_v_687_; lean_object* v___x_688_; lean_object* v_bs_x27_689_; lean_object* v___x_690_; lean_object* v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v_v_687_ = lean_array_uget(v_bs_685_, v_i_684_);
v___x_688_ = lean_unsigned_to_nat(0u);
v_bs_x27_689_ = lean_array_uset(v_bs_685_, v_i_684_, v___x_688_);
v___x_690_ = lean_box(0);
lean_inc(v_origSpan_x3f_681_);
v___x_691_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_691_, 0, v_v_687_);
lean_ctor_set(v___x_691_, 1, v_origSpan_x3f_681_);
lean_ctor_set(v___x_691_, 2, v___x_690_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3, v_diffGranularity_682_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_684_, v___x_692_);
v___x_694_ = lean_array_uset(v_bs_x27_689_, v_i_684_, v___x_691_);
v_i_684_ = v___x_693_;
v_bs_685_ = v___x_694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object* v_origSpan_x3f_696_, lean_object* v_diffGranularity_697_, lean_object* v_sz_698_, lean_object* v_i_699_, lean_object* v_bs_700_){
_start:
{
uint8_t v_diffGranularity_boxed_701_; size_t v_sz_boxed_702_; size_t v_i_boxed_703_; lean_object* v_res_704_; 
v_diffGranularity_boxed_701_ = lean_unbox(v_diffGranularity_697_);
v_sz_boxed_702_ = lean_unbox_usize(v_sz_698_);
lean_dec(v_sz_698_);
v_i_boxed_703_ = lean_unbox_usize(v_i_699_);
lean_dec(v_i_699_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_696_, v_diffGranularity_boxed_701_, v_sz_boxed_702_, v_i_boxed_703_, v_bs_700_);
return v_res_704_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object* v_ref_708_, lean_object* v_suggestions_709_, lean_object* v_origSpan_x3f_710_, lean_object* v_header_711_, lean_object* v_codeActionPrefix_x3f_712_, uint8_t v_diffGranularity_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_array_get_size(v_suggestions_709_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_nat_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
v___y_718_ = v_a_714_;
v___y_719_ = v_a_715_;
goto v___jp_717_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_codeActionPrefix_x3f_712_);
lean_dec_ref(v_header_711_);
lean_dec(v_origSpan_x3f_710_);
lean_dec_ref(v_suggestions_709_);
v___x_740_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1, &l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1);
v___x_741_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_708_, v___x_740_, v_a_714_, v_a_715_);
lean_dec(v_ref_708_);
return v___x_741_;
}
v___jp_717_:
{
size_t v_sz_720_; size_t v___x_721_; lean_object* v_hintSuggestions_722_; uint8_t v___x_723_; lean_object* v___x_724_; 
v_sz_720_ = lean_array_size(v_suggestions_709_);
v___x_721_ = ((size_t)0ULL);
v_hintSuggestions_722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_710_, v_diffGranularity_713_, v_sz_720_, v___x_721_, v_suggestions_709_);
v___x_723_ = 1;
lean_inc(v_ref_708_);
v___x_724_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_hintSuggestions_722_, v_ref_708_, v_codeActionPrefix_x3f_712_, v___x_723_, v___y_718_, v___y_719_);
lean_dec_ref(v_hintSuggestions_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
v___x_726_ = l_Lean_stringToMessageData(v_header_711_);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v_a_725_);
v___x_728_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_708_, v___x_727_, v___y_718_, v___y_719_);
lean_dec(v_ref_708_);
return v___x_728_;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_header_711_);
lean_dec(v_ref_708_);
v_a_729_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_724_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(lean_object* v_ref_742_, lean_object* v_suggestions_743_, lean_object* v_origSpan_x3f_744_, lean_object* v_header_745_, lean_object* v_codeActionPrefix_x3f_746_, lean_object* v_diffGranularity_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
uint8_t v_diffGranularity_boxed_751_; lean_object* v_res_752_; 
v_diffGranularity_boxed_751_ = lean_unbox(v_diffGranularity_747_);
v_res_752_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_742_, v_suggestions_743_, v_origSpan_x3f_744_, v_header_745_, v_codeActionPrefix_x3f_746_, v_diffGranularity_boxed_751_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object* v_ref_753_, lean_object* v_suggestions_754_, lean_object* v_origSpan_x3f_755_, lean_object* v_header_756_, lean_object* v_style_x3f_757_, lean_object* v_codeActionPrefix_x3f_758_, uint8_t v_diffGranularity_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_753_, v_suggestions_754_, v_origSpan_x3f_755_, v_header_756_, v_codeActionPrefix_x3f_758_, v_diffGranularity_759_, v_a_760_, v_a_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object* v_ref_764_, lean_object* v_suggestions_765_, lean_object* v_origSpan_x3f_766_, lean_object* v_header_767_, lean_object* v_style_x3f_768_, lean_object* v_codeActionPrefix_x3f_769_, lean_object* v_diffGranularity_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v_diffGranularity_boxed_774_; lean_object* v_res_775_; 
v_diffGranularity_boxed_774_ = lean_unbox(v_diffGranularity_770_);
v_res_775_ = l_Lean_Meta_Tactic_TryThis_addSuggestions(v_ref_764_, v_suggestions_765_, v_origSpan_x3f_766_, v_header_767_, v_style_x3f_768_, v_codeActionPrefix_x3f_769_, v_diffGranularity_boxed_774_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_style_x3f_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object* v_00_u03b1_776_, lean_object* v_ref_777_, lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_777_, v_msg_778_, v___y_779_, v___y_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object* v_00_u03b1_783_, lean_object* v_ref_784_, lean_object* v_msg_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(v_00_u03b1_783_, v_ref_784_, v_msg_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v_ref_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(lean_object* v_00_u03b1_790_, lean_object* v_msg_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_791_, v___y_792_, v___y_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___boxed(lean_object* v_00_u03b1_796_, lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(v_00_u03b1_796_, v_msg_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(lean_object* v_a_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_inc(v___y_804_);
lean_inc_ref(v___y_803_);
v___x_812_ = lean_apply_2(v_a_802_, v___y_803_, v___y_804_);
v___x_813_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_812_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg___boxed(lean_object* v_a_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(lean_object* v_00_u03b1_825_, lean_object* v_a_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___boxed(lean_object* v_00_u03b1_837_, lean_object* v_a_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(v_00_u03b1_837_, v_a_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(lean_object* v_e_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_Expr_hasMVar(v_e_849_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_e_849_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v_mctx_855_; lean_object* v___x_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v___x_859_; lean_object* v_cache_860_; lean_object* v_zetaDeltaFVarIds_861_; lean_object* v_postponed_862_; lean_object* v_diag_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_872_; 
v___x_854_ = lean_st_ref_get(v___y_850_);
v_mctx_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref(v_mctx_855_);
lean_dec(v___x_854_);
v___x_856_ = l_Lean_instantiateMVarsCore(v_mctx_855_, v_e_849_);
v_fst_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_fst_857_);
v_snd_858_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_snd_858_);
lean_dec_ref(v___x_856_);
v___x_859_ = lean_st_ref_take(v___y_850_);
v_cache_860_ = lean_ctor_get(v___x_859_, 1);
v_zetaDeltaFVarIds_861_ = lean_ctor_get(v___x_859_, 2);
v_postponed_862_ = lean_ctor_get(v___x_859_, 3);
v_diag_863_ = lean_ctor_get(v___x_859_, 4);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___x_859_, 0);
lean_dec(v_unused_873_);
v___x_865_ = v___x_859_;
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_diag_863_);
lean_inc(v_postponed_862_);
lean_inc(v_zetaDeltaFVarIds_861_);
lean_inc(v_cache_860_);
lean_dec(v___x_859_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_snd_858_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_snd_858_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_cache_860_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_zetaDeltaFVarIds_861_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_postponed_862_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v_diag_863_);
v___x_868_ = v_reuseFailAlloc_871_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_st_ref_set(v___y_850_, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_fst_857_);
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(lean_object* v_e_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_874_, v___y_875_);
lean_dec(v___y_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(lean_object* v_e_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_878_, v___y_884_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(lean_object* v_e_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_ref_906_ = lean_ctor_get(v___y_903_, 5);
v___x_907_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_inc(v_ref_906_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_ref_906_);
lean_ctor_set(v___x_912_, 1, v_a_908_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 1);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* v_initialState_927_, lean_object* v_tac_928_, lean_object* v_expectedType_x3f_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_931_, v_a_933_, v_a_935_, v_a_937_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; uint8_t v___x_941_; lean_object* v_a_943_; lean_object* v_a_954_; lean_object* v___y_965_; lean_object* v___x_968_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v___x_939_);
v___x_941_ = 0;
v___x_968_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_initialState_927_, v___x_941_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec_ref(v___x_968_);
v___x_969_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_969_, 0, v_tac_928_);
v___x_970_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_970_, 0, lean_box(0));
lean_closure_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v___x_970_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref(v___x_971_);
if (lean_obj_tag(v_expectedType_x3f_929_) == 1)
{
lean_object* v_val_972_; lean_object* v___x_973_; 
v_val_972_ = lean_ctor_get(v_expectedType_x3f_929_, 0);
lean_inc(v_val_972_);
lean_dec_ref(v_expectedType_x3f_929_);
v___x_973_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_931_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = l_Lean_MVarId_getType(v_a_974_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v_a_980_; uint8_t v___x_981_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_976_, v_a_935_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_val_972_, v_a_935_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_expr_eqv(v_a_978_, v_a_980_);
lean_dec(v_a_980_);
lean_dec(v_a_978_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
v___x_983_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v___x_982_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
v___y_965_ = v___x_983_;
goto v___jp_964_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = lean_box(0);
v_a_954_ = v___x_984_;
goto v___jp_953_;
}
}
else
{
lean_object* v_a_985_; 
lean_dec(v_val_972_);
v_a_985_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_975_);
v_a_943_ = v_a_985_;
goto v___jp_942_;
}
}
else
{
lean_object* v_a_986_; 
lean_dec(v_val_972_);
v_a_986_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_973_);
v_a_943_ = v_a_986_;
goto v___jp_942_;
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v_expectedType_x3f_929_);
v___x_987_ = lean_box(0);
v_a_954_ = v___x_987_;
goto v___jp_953_;
}
}
else
{
lean_dec(v_expectedType_x3f_929_);
v___y_965_ = v___x_971_;
goto v___jp_964_;
}
}
else
{
lean_dec(v_a_940_);
lean_dec(v_expectedType_x3f_929_);
lean_dec(v_tac_928_);
return v___x_968_;
}
v___jp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_940_, v___x_941_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_952_);
v___x_946_ = v___x_944_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_dec(v___x_944_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
lean_ctor_set(v___x_946_, 0, v_a_943_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_943_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_dec_ref(v_a_943_);
return v___x_944_;
}
}
v___jp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_940_, v___x_941_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
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
lean_ctor_set(v___x_957_, 0, v_a_954_);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
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
return v___x_955_;
}
}
v___jp_964_:
{
if (lean_obj_tag(v___y_965_) == 0)
{
lean_object* v_a_966_; 
v_a_966_ = lean_ctor_get(v___y_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v___y_965_);
v_a_954_ = v_a_966_;
goto v___jp_953_;
}
else
{
lean_object* v_a_967_; 
v_a_967_ = lean_ctor_get(v___y_965_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___y_965_);
v_a_943_ = v_a_967_;
goto v___jp_942_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_expectedType_x3f_929_);
lean_dec(v_tac_928_);
lean_dec_ref(v_initialState_927_);
v_a_988_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_939_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_939_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object* v_initialState_996_, lean_object* v_tac_997_, lean_object* v_expectedType_x3f_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_996_, v_tac_997_, v_expectedType_x3f_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(lean_object* v_00_u03b1_1009_, lean_object* v_msg_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_1010_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2(v_00_u03b1_1021_, v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* v_tac_1070_, lean_object* v_msg_1071_, lean_object* v_initialState_1072_, lean_object* v_expectedType_x3f_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___y_1084_; lean_object* v___y_1085_; uint8_t v___y_1086_; lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1075_, v_a_1077_, v_a_1079_, v_a_1081_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v___x_1106_);
lean_inc(v_expectedType_x3f_1073_);
lean_inc(v_tac_1070_);
lean_inc_ref(v_initialState_1072_);
v___x_1108_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1072_, v_tac_1070_, v_expectedType_x3f_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_a_1107_);
lean_dec(v_expectedType_x3f_1073_);
lean_dec_ref(v_initialState_1072_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1108_, 0);
lean_dec(v_unused_1118_);
v___x_1110_ = v___x_1108_;
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v___x_1108_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1117_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_tac_1070_);
lean_ctor_set(v___x_1112_, 1, v_msg_1071_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1113_);
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1187_; 
v_a_1119_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1121_ = v___x_1108_;
v_isShared_1122_ = v_isSharedCheck_1187_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1108_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1187_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
uint8_t v___y_1124_; uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_Exception_isInterrupt(v_a_1119_);
if (v___x_1185_ == 0)
{
uint8_t v___x_1186_; 
lean_inc(v_a_1119_);
v___x_1186_ = l_Lean_Exception_isRuntime(v_a_1119_);
v___y_1124_ = v___x_1186_;
goto v___jp_1123_;
}
else
{
v___y_1124_ = v___x_1185_;
goto v___jp_1123_;
}
v___jp_1123_:
{
if (v___y_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_del_object(v___x_1121_);
lean_dec(v_a_1119_);
v___x_1125_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1107_, v___y_1124_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_ref_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v___x_1125_);
v_ref_1126_ = lean_ctor_get(v_a_1080_, 5);
v___x_1127_ = l_Lean_SourceInfo_fromRef(v_ref_1126_, v___y_1124_);
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2));
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3));
lean_inc_n(v___x_1127_, 6);
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1127_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5));
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7));
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11));
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12));
v___x_1136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1127_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_node1(v___x_1127_, v___x_1134_, v___x_1136_);
v___x_1138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1127_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_Syntax_node3(v___x_1127_, v___x_1133_, v___x_1137_, v___x_1139_, v_tac_1070_);
v___x_1141_ = l_Lean_Syntax_node1(v___x_1127_, v___x_1132_, v___x_1140_);
v___x_1142_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1075_, v_a_1077_, v_a_1079_, v_a_1081_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
lean_inc_n(v___x_1127_, 2);
v___x_1144_ = l_Lean_Syntax_node1(v___x_1127_, v___x_1131_, v___x_1141_);
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1127_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node3(v___x_1127_, v___x_1128_, v___x_1130_, v___x_1144_, v___x_1146_);
lean_inc(v___x_1147_);
v___x_1148_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1072_, v___x_1147_, v_expectedType_x3f_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_a_1143_);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v___x_1148_, 0);
lean_dec(v_unused_1162_);
v___x_1150_ = v___x_1148_;
v_isShared_1151_ = v_isSharedCheck_1161_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v___x_1148_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1161_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_msg_1071_);
v___x_1154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1147_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1157_);
v___x_1159_ = v___x_1150_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1163_; uint8_t v___x_1164_; 
lean_dec(v___x_1147_);
lean_dec_ref(v_msg_1071_);
v_a_1163_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1148_);
v___x_1164_ = l_Lean_Exception_isInterrupt(v_a_1163_);
if (v___x_1164_ == 0)
{
uint8_t v___x_1165_; 
lean_inc(v_a_1163_);
v___x_1165_ = l_Lean_Exception_isRuntime(v_a_1163_);
v___y_1084_ = v_a_1163_;
v___y_1085_ = v_a_1143_;
v___y_1086_ = v___x_1165_;
goto v___jp_1083_;
}
else
{
v___y_1084_ = v_a_1163_;
v___y_1085_ = v_a_1143_;
v___y_1086_ = v___x_1164_;
goto v___jp_1083_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v___x_1141_);
lean_dec_ref(v___x_1130_);
lean_dec(v___x_1127_);
lean_dec(v_expectedType_x3f_1073_);
lean_dec_ref(v_initialState_1072_);
lean_dec_ref(v_msg_1071_);
v_a_1166_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1142_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1142_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_expectedType_x3f_1073_);
lean_dec_ref(v_initialState_1072_);
lean_dec_ref(v_msg_1071_);
lean_dec(v_tac_1070_);
v_a_1174_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1125_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1125_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v___x_1183_; 
lean_dec(v_a_1107_);
lean_dec(v_expectedType_x3f_1073_);
lean_dec_ref(v_initialState_1072_);
lean_dec_ref(v_msg_1071_);
lean_dec(v_tac_1070_);
if (v_isShared_1122_ == 0)
{
v___x_1183_ = v___x_1121_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1119_);
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
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_expectedType_x3f_1073_);
lean_dec_ref(v_initialState_1072_);
lean_dec_ref(v_msg_1071_);
lean_dec(v_tac_1070_);
v_a_1188_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1106_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1106_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
v___jp_1083_:
{
if (v___y_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v___y_1084_);
v___x_1087_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_1085_, v___y_1086_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1096_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1087_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1087_);
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
else
{
lean_object* v___x_1105_; 
lean_dec_ref(v___y_1085_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___y_1084_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object* v_tac_1196_, lean_object* v_msg_1197_, lean_object* v_initialState_1198_, lean_object* v_expectedType_x3f_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_tac_1196_, v_msg_1197_, v_initialState_1198_, v_expectedType_x3f_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* v_targetKind_1219_, lean_object* v_invalidTactic_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_targetKind_1219_);
v___x_1223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_indentD(v_invalidTactic_1220_);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object* v_e_1247_, uint8_t v_useRefine_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___x_1259_; 
lean_inc_ref(v_e_1247_);
v___x_1259_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_1247_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_tac_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref(v___x_1259_);
if (v_useRefine_1248_ == 0)
{
lean_object* v_ref_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_ref_1275_ = lean_ctor_get(v___y_1251_, 5);
v___x_1276_ = l_Lean_SourceInfo_fromRef(v_ref_1275_, v_useRefine_1248_);
v___x_1277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4));
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5));
lean_inc(v___x_1276_);
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1276_);
lean_ctor_set(v___x_1279_, 1, v___x_1277_);
v___x_1280_ = l_Lean_Syntax_node2(v___x_1276_, v___x_1278_, v___x_1279_, v_a_1260_);
v_tac_1262_ = v___x_1280_;
v___y_1263_ = v___y_1249_;
v___y_1264_ = v___y_1250_;
v___y_1265_ = v___y_1251_;
v___y_1266_ = v___y_1252_;
goto v___jp_1261_;
}
else
{
lean_object* v_ref_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_ref_1281_ = lean_ctor_get(v___y_1251_, 5);
v___x_1282_ = 0;
v___x_1283_ = l_Lean_SourceInfo_fromRef(v_ref_1281_, v___x_1282_);
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6));
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7));
lean_inc(v___x_1283_);
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1283_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
v___x_1287_ = l_Lean_Syntax_node2(v___x_1283_, v___x_1285_, v___x_1286_, v_a_1260_);
v_tac_1262_ = v___x_1287_;
v___y_1263_ = v___y_1249_;
v___y_1264_ = v___y_1250_;
v___y_1265_ = v___y_1251_;
v___y_1266_ = v___y_1252_;
goto v___jp_1261_;
}
v___jp_1261_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_Lean_MessageData_ofExpr(v_e_1247_);
v___x_1268_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1267_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (v_useRefine_1248_ == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_a_1269_);
v___y_1255_ = v_tac_1262_;
v___y_1256_ = v___x_1271_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1268_);
v___x_1273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v_a_1272_);
v___y_1255_ = v_tac_1262_;
v___y_1256_ = v___x_1274_;
goto v___jp_1254_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_e_1247_);
v_a_1288_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1259_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1259_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
v___jp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1255_);
lean_ctor_set(v___x_1257_, 1, v___y_1256_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object* v_e_1296_, lean_object* v_useRefine_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v_useRefine_boxed_1303_; lean_object* v_res_1304_; 
v_useRefine_boxed_1303_ = lean_unbox(v_useRefine_1297_);
v_res_1304_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_1296_, v_useRefine_boxed_1303_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* v_e_1305_, uint8_t v_useRefine_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_fileName_1313_; lean_object* v_fileMap_1314_; lean_object* v_options_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_ref_1317_; lean_object* v_currNamespace_1318_; lean_object* v_openDecls_1319_; lean_object* v_initHeartbeats_1320_; lean_object* v_maxHeartbeats_1321_; lean_object* v_quotContext_1322_; lean_object* v_currMacroScope_1323_; lean_object* v_cancelTk_x3f_1324_; uint8_t v_suppressElabErrors_1325_; lean_object* v_inheritedTraceOptions_1326_; lean_object* v_env_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v_fileName_1336_; lean_object* v_fileMap_1337_; lean_object* v_currRecDepth_1338_; lean_object* v_ref_1339_; lean_object* v_currNamespace_1340_; lean_object* v_openDecls_1341_; lean_object* v_initHeartbeats_1342_; lean_object* v_maxHeartbeats_1343_; lean_object* v_quotContext_1344_; lean_object* v_currMacroScope_1345_; lean_object* v_cancelTk_x3f_1346_; uint8_t v_suppressElabErrors_1347_; lean_object* v_inheritedTraceOptions_1348_; lean_object* v___y_1349_; uint8_t v___y_1355_; uint8_t v___x_1376_; 
v___x_1312_ = lean_st_ref_get(v_a_1310_);
v_fileName_1313_ = lean_ctor_get(v_a_1309_, 0);
v_fileMap_1314_ = lean_ctor_get(v_a_1309_, 1);
v_options_1315_ = lean_ctor_get(v_a_1309_, 2);
v_currRecDepth_1316_ = lean_ctor_get(v_a_1309_, 3);
v_ref_1317_ = lean_ctor_get(v_a_1309_, 5);
v_currNamespace_1318_ = lean_ctor_get(v_a_1309_, 6);
v_openDecls_1319_ = lean_ctor_get(v_a_1309_, 7);
v_initHeartbeats_1320_ = lean_ctor_get(v_a_1309_, 8);
v_maxHeartbeats_1321_ = lean_ctor_get(v_a_1309_, 9);
v_quotContext_1322_ = lean_ctor_get(v_a_1309_, 10);
v_currMacroScope_1323_ = lean_ctor_get(v_a_1309_, 11);
v_cancelTk_x3f_1324_ = lean_ctor_get(v_a_1309_, 12);
v_suppressElabErrors_1325_ = lean_ctor_get_uint8(v_a_1309_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1326_ = lean_ctor_get(v_a_1309_, 13);
v_env_1327_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1327_);
lean_dec(v___x_1312_);
v___x_1328_ = lean_box(v_useRefine_1306_);
v___f_1329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1329_, 0, v_e_1305_);
lean_closure_set(v___f_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_pp_mvars;
v___x_1331_ = 0;
lean_inc_ref(v_options_1315_);
v___x_1332_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_1315_, v___x_1330_, v___x_1331_);
v___x_1333_ = l_Lean_diagnostics;
v___x_1334_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_1332_, v___x_1333_);
v___x_1376_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1327_);
lean_dec_ref(v_env_1327_);
if (v___x_1376_ == 0)
{
if (v___x_1334_ == 0)
{
v_fileName_1336_ = v_fileName_1313_;
v_fileMap_1337_ = v_fileMap_1314_;
v_currRecDepth_1338_ = v_currRecDepth_1316_;
v_ref_1339_ = v_ref_1317_;
v_currNamespace_1340_ = v_currNamespace_1318_;
v_openDecls_1341_ = v_openDecls_1319_;
v_initHeartbeats_1342_ = v_initHeartbeats_1320_;
v_maxHeartbeats_1343_ = v_maxHeartbeats_1321_;
v_quotContext_1344_ = v_quotContext_1322_;
v_currMacroScope_1345_ = v_currMacroScope_1323_;
v_cancelTk_x3f_1346_ = v_cancelTk_x3f_1324_;
v_suppressElabErrors_1347_ = v_suppressElabErrors_1325_;
v_inheritedTraceOptions_1348_ = v_inheritedTraceOptions_1326_;
v___y_1349_ = v_a_1310_;
goto v___jp_1335_;
}
else
{
v___y_1355_ = v___x_1376_;
goto v___jp_1354_;
}
}
else
{
v___y_1355_ = v___x_1334_;
goto v___jp_1354_;
}
v___jp_1335_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1350_ = l_Lean_maxRecDepth;
v___x_1351_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_1332_, v___x_1350_);
lean_inc_ref(v_inheritedTraceOptions_1348_);
lean_inc(v_cancelTk_x3f_1346_);
lean_inc(v_currMacroScope_1345_);
lean_inc(v_quotContext_1344_);
lean_inc(v_maxHeartbeats_1343_);
lean_inc(v_initHeartbeats_1342_);
lean_inc(v_openDecls_1341_);
lean_inc(v_currNamespace_1340_);
lean_inc(v_ref_1339_);
lean_inc(v_currRecDepth_1338_);
lean_inc_ref(v_fileMap_1337_);
lean_inc_ref(v_fileName_1336_);
v___x_1352_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1352_, 0, v_fileName_1336_);
lean_ctor_set(v___x_1352_, 1, v_fileMap_1337_);
lean_ctor_set(v___x_1352_, 2, v___x_1332_);
lean_ctor_set(v___x_1352_, 3, v_currRecDepth_1338_);
lean_ctor_set(v___x_1352_, 4, v___x_1351_);
lean_ctor_set(v___x_1352_, 5, v_ref_1339_);
lean_ctor_set(v___x_1352_, 6, v_currNamespace_1340_);
lean_ctor_set(v___x_1352_, 7, v_openDecls_1341_);
lean_ctor_set(v___x_1352_, 8, v_initHeartbeats_1342_);
lean_ctor_set(v___x_1352_, 9, v_maxHeartbeats_1343_);
lean_ctor_set(v___x_1352_, 10, v_quotContext_1344_);
lean_ctor_set(v___x_1352_, 11, v_currMacroScope_1345_);
lean_ctor_set(v___x_1352_, 12, v_cancelTk_x3f_1346_);
lean_ctor_set(v___x_1352_, 13, v_inheritedTraceOptions_1348_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*14, v___x_1334_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*14 + 1, v_suppressElabErrors_1347_);
v___x_1353_ = l_Lean_Meta_withExposedNames___redArg(v___f_1329_, v_a_1307_, v_a_1308_, v___x_1352_, v___y_1349_);
lean_dec_ref(v___x_1352_);
return v___x_1353_;
}
v___jp_1354_:
{
if (v___y_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v_env_1357_; lean_object* v_nextMacroScope_1358_; lean_object* v_ngen_1359_; lean_object* v_auxDeclNGen_1360_; lean_object* v_traceState_1361_; lean_object* v_messages_1362_; lean_object* v_infoState_1363_; lean_object* v_snapshotTasks_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1374_; 
v___x_1356_ = lean_st_ref_take(v_a_1310_);
v_env_1357_ = lean_ctor_get(v___x_1356_, 0);
v_nextMacroScope_1358_ = lean_ctor_get(v___x_1356_, 1);
v_ngen_1359_ = lean_ctor_get(v___x_1356_, 2);
v_auxDeclNGen_1360_ = lean_ctor_get(v___x_1356_, 3);
v_traceState_1361_ = lean_ctor_get(v___x_1356_, 4);
v_messages_1362_ = lean_ctor_get(v___x_1356_, 6);
v_infoState_1363_ = lean_ctor_get(v___x_1356_, 7);
v_snapshotTasks_1364_ = lean_ctor_get(v___x_1356_, 8);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v___x_1356_, 5);
lean_dec(v_unused_1375_);
v___x_1366_ = v___x_1356_;
v_isShared_1367_ = v_isSharedCheck_1374_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snapshotTasks_1364_);
lean_inc(v_infoState_1363_);
lean_inc(v_messages_1362_);
lean_inc(v_traceState_1361_);
lean_inc(v_auxDeclNGen_1360_);
lean_inc(v_ngen_1359_);
lean_inc(v_nextMacroScope_1358_);
lean_inc(v_env_1357_);
lean_dec(v___x_1356_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1374_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1368_ = l_Lean_Kernel_enableDiag(v_env_1357_, v___x_1334_);
v___x_1369_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 5, v___x_1369_);
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1371_ = v___x_1366_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_nextMacroScope_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_ngen_1359_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_auxDeclNGen_1360_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_traceState_1361_);
lean_ctor_set(v_reuseFailAlloc_1373_, 5, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 6, v_messages_1362_);
lean_ctor_set(v_reuseFailAlloc_1373_, 7, v_infoState_1363_);
lean_ctor_set(v_reuseFailAlloc_1373_, 8, v_snapshotTasks_1364_);
v___x_1371_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_st_ref_set(v_a_1310_, v___x_1371_);
v_fileName_1336_ = v_fileName_1313_;
v_fileMap_1337_ = v_fileMap_1314_;
v_currRecDepth_1338_ = v_currRecDepth_1316_;
v_ref_1339_ = v_ref_1317_;
v_currNamespace_1340_ = v_currNamespace_1318_;
v_openDecls_1341_ = v_openDecls_1319_;
v_initHeartbeats_1342_ = v_initHeartbeats_1320_;
v_maxHeartbeats_1343_ = v_maxHeartbeats_1321_;
v_quotContext_1344_ = v_quotContext_1322_;
v_currMacroScope_1345_ = v_currMacroScope_1323_;
v_cancelTk_x3f_1346_ = v_cancelTk_x3f_1324_;
v_suppressElabErrors_1347_ = v_suppressElabErrors_1325_;
v_inheritedTraceOptions_1348_ = v_inheritedTraceOptions_1326_;
v___y_1349_ = v_a_1310_;
goto v___jp_1335_;
}
}
}
else
{
v_fileName_1336_ = v_fileName_1313_;
v_fileMap_1337_ = v_fileMap_1314_;
v_currRecDepth_1338_ = v_currRecDepth_1316_;
v_ref_1339_ = v_ref_1317_;
v_currNamespace_1340_ = v_currNamespace_1318_;
v_openDecls_1341_ = v_openDecls_1319_;
v_initHeartbeats_1342_ = v_initHeartbeats_1320_;
v_maxHeartbeats_1343_ = v_maxHeartbeats_1321_;
v_quotContext_1344_ = v_quotContext_1322_;
v_currMacroScope_1345_ = v_currMacroScope_1323_;
v_cancelTk_x3f_1346_ = v_cancelTk_x3f_1324_;
v_suppressElabErrors_1347_ = v_suppressElabErrors_1325_;
v_inheritedTraceOptions_1348_ = v_inheritedTraceOptions_1326_;
v___y_1349_ = v_a_1310_;
goto v___jp_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* v_e_1377_, lean_object* v_useRefine_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
uint8_t v_useRefine_boxed_1384_; lean_object* v_res_1385_; 
v_useRefine_boxed_1384_ = lean_unbox(v_useRefine_1378_);
v_res_1385_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1377_, v_useRefine_boxed_1384_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(lean_object* v_as_1389_, size_t v_sz_1390_, size_t v_i_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_usize_dec_lt(v_i_1391_, v_sz_1390_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v_b_1392_);
return v___x_1399_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1401_; 
v_a_1400_ = lean_array_uget_borrowed(v_as_1389_, v_i_1391_);
lean_inc(v_a_1400_);
v___x_1401_ = l_Lean_MVarId_getType(v_a_1400_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_1402_, v___y_1394_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___boxed), 6, 1);
lean_closure_set(v___x_1405_, 0, v_a_1404_);
v___x_1406_ = l_Lean_Meta_withExposedNames___redArg(v___x_1405_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1));
v___x_1409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_a_1407_);
v___x_1410_ = l_Std_Format_defWidth;
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = l_Std_Format_pretty(v___x_1409_, v___x_1410_, v___x_1411_, v___x_1411_);
v___x_1413_ = lean_string_append(v_b_1392_, v___x_1412_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_add(v_i_1391_, v___x_1414_);
v_i_1391_ = v___x_1415_;
v_b_1392_ = v___x_1413_;
goto _start;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_b_1392_);
v_a_1417_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1406_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1406_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_b_1392_);
v_a_1425_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1403_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1403_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_b_1392_);
v_a_1433_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1401_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1401_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(lean_object* v_as_1441_, lean_object* v_sz_1442_, lean_object* v_i_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; lean_object* v_res_1452_; 
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1442_);
lean_dec(v_sz_1442_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1443_);
lean_dec(v_i_1443_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1441_, v_sz_boxed_1450_, v_i_boxed_1451_, v_b_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v_as_1441_);
return v_res_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2));
v___x_1458_ = l_Lean_stringToMessageData(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t v_addSubgoalsMsg_1464_, lean_object* v_checkState_x3f_1465_, lean_object* v_e_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v_postInfo_x3f_1479_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1503_; uint8_t v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___x_1592_; lean_object* v_fileName_1593_; lean_object* v_fileMap_1594_; lean_object* v_options_1595_; lean_object* v_currRecDepth_1596_; lean_object* v_ref_1597_; lean_object* v_currNamespace_1598_; lean_object* v_openDecls_1599_; lean_object* v_initHeartbeats_1600_; lean_object* v_maxHeartbeats_1601_; lean_object* v_quotContext_1602_; lean_object* v_currMacroScope_1603_; lean_object* v_cancelTk_x3f_1604_; uint8_t v_suppressElabErrors_1605_; lean_object* v_inheritedTraceOptions_1606_; lean_object* v_env_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v_fileName_1614_; lean_object* v_fileMap_1615_; lean_object* v_currRecDepth_1616_; lean_object* v_ref_1617_; lean_object* v_currNamespace_1618_; lean_object* v_openDecls_1619_; lean_object* v_initHeartbeats_1620_; lean_object* v_maxHeartbeats_1621_; lean_object* v_quotContext_1622_; lean_object* v_currMacroScope_1623_; lean_object* v_cancelTk_x3f_1624_; uint8_t v_suppressElabErrors_1625_; lean_object* v_inheritedTraceOptions_1626_; lean_object* v___y_1627_; uint8_t v___y_1646_; uint8_t v___x_1667_; 
v___x_1592_ = lean_st_ref_get(v_a_1474_);
v_fileName_1593_ = lean_ctor_get(v_a_1473_, 0);
v_fileMap_1594_ = lean_ctor_get(v_a_1473_, 1);
v_options_1595_ = lean_ctor_get(v_a_1473_, 2);
v_currRecDepth_1596_ = lean_ctor_get(v_a_1473_, 3);
v_ref_1597_ = lean_ctor_get(v_a_1473_, 5);
v_currNamespace_1598_ = lean_ctor_get(v_a_1473_, 6);
v_openDecls_1599_ = lean_ctor_get(v_a_1473_, 7);
v_initHeartbeats_1600_ = lean_ctor_get(v_a_1473_, 8);
v_maxHeartbeats_1601_ = lean_ctor_get(v_a_1473_, 9);
v_quotContext_1602_ = lean_ctor_get(v_a_1473_, 10);
v_currMacroScope_1603_ = lean_ctor_get(v_a_1473_, 11);
v_cancelTk_x3f_1604_ = lean_ctor_get(v_a_1473_, 12);
v_suppressElabErrors_1605_ = lean_ctor_get_uint8(v_a_1473_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1606_ = lean_ctor_get(v_a_1473_, 13);
v_env_1607_ = lean_ctor_get(v___x_1592_, 0);
lean_inc_ref(v_env_1607_);
lean_dec(v___x_1592_);
v___x_1608_ = l_Lean_pp_mvars;
v___x_1609_ = 0;
lean_inc_ref(v_options_1595_);
v___x_1610_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_1595_, v___x_1608_, v___x_1609_);
v___x_1611_ = l_Lean_diagnostics;
v___x_1612_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_1610_, v___x_1611_);
v___x_1667_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1607_);
lean_dec_ref(v_env_1607_);
if (v___x_1667_ == 0)
{
if (v___x_1612_ == 0)
{
v_fileName_1614_ = v_fileName_1593_;
v_fileMap_1615_ = v_fileMap_1594_;
v_currRecDepth_1616_ = v_currRecDepth_1596_;
v_ref_1617_ = v_ref_1597_;
v_currNamespace_1618_ = v_currNamespace_1598_;
v_openDecls_1619_ = v_openDecls_1599_;
v_initHeartbeats_1620_ = v_initHeartbeats_1600_;
v_maxHeartbeats_1621_ = v_maxHeartbeats_1601_;
v_quotContext_1622_ = v_quotContext_1602_;
v_currMacroScope_1623_ = v_currMacroScope_1603_;
v_cancelTk_x3f_1624_ = v_cancelTk_x3f_1604_;
v_suppressElabErrors_1625_ = v_suppressElabErrors_1605_;
v_inheritedTraceOptions_1626_ = v_inheritedTraceOptions_1606_;
v___y_1627_ = v_a_1474_;
goto v___jp_1613_;
}
else
{
v___y_1646_ = v___x_1667_;
goto v___jp_1645_;
}
}
else
{
v___y_1646_ = v___x_1612_;
goto v___jp_1645_;
}
v___jp_1476_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___y_1478_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___y_1477_);
v___x_1484_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1481_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v_postInfo_x3f_1479_);
lean_ctor_set(v___x_1484_, 3, v___x_1482_);
lean_ctor_set(v___x_1484_, 4, v___x_1483_);
lean_ctor_set(v___x_1484_, 5, v___x_1482_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
v___jp_1487_:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_box(0);
v___y_1477_ = v___y_1488_;
v___y_1478_ = v___y_1489_;
v_postInfo_x3f_1479_ = v___x_1490_;
goto v___jp_1476_;
}
v___jp_1491_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_inc_ref(v___y_1494_);
v___x_1495_ = l_Lean_stringToMessageData(v___y_1494_);
lean_inc_ref(v___y_1492_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1492_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_1498_, v___y_1493_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
v___jp_1502_:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1466_, v___y_1507_, v_a_1471_, v_a_1472_, v___y_1506_, v___y_1503_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1583_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1583_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1583_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
if (lean_obj_tag(v_checkState_x3f_1465_) == 1)
{
lean_object* v_fst_1513_; lean_object* v_snd_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1511_);
v_fst_1513_ = lean_ctor_get(v_a_1509_, 0);
v_snd_1514_ = lean_ctor_get(v_a_1509_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_a_1509_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1516_ = v_a_1509_;
v_isShared_1517_ = v_isSharedCheck_1566_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_snd_1514_);
lean_inc(v_fst_1513_);
lean_dec(v_a_1509_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1566_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_val_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_val_1518_ = lean_ctor_get(v_checkState_x3f_1465_, 0);
lean_inc(v_val_1518_);
lean_dec_ref(v_checkState_x3f_1465_);
v___x_1519_ = lean_box(0);
lean_inc(v_snd_1514_);
v___x_1520_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_1513_, v_snd_1514_, v_val_1518_, v___x_1519_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v___y_1506_, v___y_1503_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
if (lean_obj_tag(v_a_1521_) == 1)
{
lean_object* v_val_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1548_; 
lean_del_object(v___x_1516_);
lean_dec(v_snd_1514_);
v_val_1522_ = lean_ctor_get(v_a_1521_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_a_1521_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1524_ = v_a_1521_;
v_isShared_1525_ = v_isSharedCheck_1548_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_val_1522_);
lean_dec(v_a_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1548_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
if (v_addSubgoalsMsg_1464_ == 0)
{
lean_object* v_fst_1526_; lean_object* v_snd_1527_; 
lean_del_object(v___x_1524_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
v_fst_1526_ = lean_ctor_get(v_val_1522_, 0);
lean_inc(v_fst_1526_);
v_snd_1527_ = lean_ctor_get(v_val_1522_, 1);
lean_inc(v_snd_1527_);
lean_dec(v_val_1522_);
v___y_1488_ = v_snd_1527_;
v___y_1489_ = v_fst_1526_;
goto v___jp_1487_;
}
else
{
if (v___y_1504_ == 0)
{
lean_object* v_fst_1528_; lean_object* v_snd_1529_; lean_object* v___x_1530_; size_t v_sz_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v_fst_1528_ = lean_ctor_get(v_val_1522_, 0);
lean_inc(v_fst_1528_);
v_snd_1529_ = lean_ctor_get(v_val_1522_, 1);
lean_inc(v_snd_1529_);
lean_dec(v_val_1522_);
v___x_1530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4));
v_sz_1531_ = lean_array_size(v___y_1505_);
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v___y_1505_, v_sz_1531_, v___x_1532_, v___x_1530_, v_a_1471_, v_a_1472_, v___y_1506_, v___y_1503_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v_a_1534_);
v___x_1536_ = v___x_1524_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
v___y_1477_ = v_snd_1529_;
v___y_1478_ = v_fst_1528_;
v_postInfo_x3f_1479_ = v___x_1536_;
goto v___jp_1476_;
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_del_object(v___x_1524_);
v_a_1538_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1533_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1533_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_fst_1546_; lean_object* v_snd_1547_; 
lean_del_object(v___x_1524_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
v_fst_1546_ = lean_ctor_get(v_val_1522_, 0);
lean_inc(v_fst_1546_);
v_snd_1547_ = lean_ctor_get(v_val_1522_, 1);
lean_inc(v_snd_1547_);
lean_dec(v_val_1522_);
v___y_1488_ = v_snd_1547_;
v___y_1489_ = v_fst_1546_;
goto v___jp_1487_;
}
}
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v_a_1521_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
v___x_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 7);
lean_ctor_set(v___x_1516_, 0, v___x_1549_);
v___x_1551_ = v___x_1516_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_snd_1514_);
v___x_1551_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6);
if (v___y_1507_ == 0)
{
lean_object* v___x_1555_; 
v___x_1555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_1492_ = v___x_1554_;
v___y_1493_ = v___x_1553_;
v___y_1494_ = v___x_1555_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7));
v___y_1492_ = v___x_1554_;
v___y_1493_ = v___x_1553_;
v___y_1494_ = v___x_1556_;
goto v___jp_1491_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1516_);
lean_dec(v_snd_1514_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
v_a_1558_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1520_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1520_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_fst_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_checkState_x3f_1465_);
v_fst_1567_ = lean_ctor_get(v_a_1509_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1509_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_a_1509_, 1);
lean_dec(v_unused_1582_);
v___x_1569_ = v_a_1509_;
v_isShared_1570_ = v_isSharedCheck_1581_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_fst_1567_);
lean_dec(v_a_1509_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1581_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v_fst_1567_);
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_fst_1567_);
v___x_1573_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
lean_ctor_set(v___x_1575_, 2, v___x_1574_);
lean_ctor_set(v___x_1575_, 3, v___x_1574_);
lean_ctor_set(v___x_1575_, 4, v___x_1574_);
lean_ctor_set(v___x_1575_, 5, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1576_);
v___x_1578_ = v___x_1511_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_checkState_x3f_1465_);
v_a_1584_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1508_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1508_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
v___jp_1613_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = l_Lean_maxRecDepth;
v___x_1629_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_1610_, v___x_1628_);
lean_inc_ref(v_inheritedTraceOptions_1626_);
lean_inc(v_cancelTk_x3f_1624_);
lean_inc(v_currMacroScope_1623_);
lean_inc(v_quotContext_1622_);
lean_inc(v_maxHeartbeats_1621_);
lean_inc(v_initHeartbeats_1620_);
lean_inc(v_openDecls_1619_);
lean_inc(v_currNamespace_1618_);
lean_inc(v_ref_1617_);
lean_inc(v_currRecDepth_1616_);
lean_inc_ref(v_fileMap_1615_);
lean_inc_ref(v_fileName_1614_);
v___x_1630_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1630_, 0, v_fileName_1614_);
lean_ctor_set(v___x_1630_, 1, v_fileMap_1615_);
lean_ctor_set(v___x_1630_, 2, v___x_1610_);
lean_ctor_set(v___x_1630_, 3, v_currRecDepth_1616_);
lean_ctor_set(v___x_1630_, 4, v___x_1629_);
lean_ctor_set(v___x_1630_, 5, v_ref_1617_);
lean_ctor_set(v___x_1630_, 6, v_currNamespace_1618_);
lean_ctor_set(v___x_1630_, 7, v_openDecls_1619_);
lean_ctor_set(v___x_1630_, 8, v_initHeartbeats_1620_);
lean_ctor_set(v___x_1630_, 9, v_maxHeartbeats_1621_);
lean_ctor_set(v___x_1630_, 10, v_quotContext_1622_);
lean_ctor_set(v___x_1630_, 11, v_currMacroScope_1623_);
lean_ctor_set(v___x_1630_, 12, v_cancelTk_x3f_1624_);
lean_ctor_set(v___x_1630_, 13, v_inheritedTraceOptions_1626_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*14, v___x_1612_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*14 + 1, v_suppressElabErrors_1625_);
lean_inc_ref(v_e_1466_);
v___x_1631_ = l_Lean_Meta_getMVars(v_e_1466_, v_a_1471_, v_a_1472_, v___x_1630_, v___y_1627_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = lean_array_get_size(v_a_1632_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; 
v___x_1636_ = 1;
v___y_1503_ = v___y_1627_;
v___y_1504_ = v___x_1635_;
v___y_1505_ = v_a_1632_;
v___y_1506_ = v___x_1630_;
v___y_1507_ = v___x_1636_;
goto v___jp_1502_;
}
else
{
v___y_1503_ = v___y_1627_;
v___y_1504_ = v___x_1635_;
v___y_1505_ = v_a_1632_;
v___y_1506_ = v___x_1630_;
v___y_1507_ = v___x_1609_;
goto v___jp_1502_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v___x_1630_);
lean_dec_ref(v_e_1466_);
lean_dec(v_checkState_x3f_1465_);
v_a_1637_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1631_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1631_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
v___jp_1645_:
{
if (v___y_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v_env_1648_; lean_object* v_nextMacroScope_1649_; lean_object* v_ngen_1650_; lean_object* v_auxDeclNGen_1651_; lean_object* v_traceState_1652_; lean_object* v_messages_1653_; lean_object* v_infoState_1654_; lean_object* v_snapshotTasks_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1665_; 
v___x_1647_ = lean_st_ref_take(v_a_1474_);
v_env_1648_ = lean_ctor_get(v___x_1647_, 0);
v_nextMacroScope_1649_ = lean_ctor_get(v___x_1647_, 1);
v_ngen_1650_ = lean_ctor_get(v___x_1647_, 2);
v_auxDeclNGen_1651_ = lean_ctor_get(v___x_1647_, 3);
v_traceState_1652_ = lean_ctor_get(v___x_1647_, 4);
v_messages_1653_ = lean_ctor_get(v___x_1647_, 6);
v_infoState_1654_ = lean_ctor_get(v___x_1647_, 7);
v_snapshotTasks_1655_ = lean_ctor_get(v___x_1647_, 8);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___x_1647_, 5);
lean_dec(v_unused_1666_);
v___x_1657_ = v___x_1647_;
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_snapshotTasks_1655_);
lean_inc(v_infoState_1654_);
lean_inc(v_messages_1653_);
lean_inc(v_traceState_1652_);
lean_inc(v_auxDeclNGen_1651_);
lean_inc(v_ngen_1650_);
lean_inc(v_nextMacroScope_1649_);
lean_inc(v_env_1648_);
lean_dec(v___x_1647_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1659_ = l_Lean_Kernel_enableDiag(v_env_1648_, v___x_1612_);
v___x_1660_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 5, v___x_1660_);
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_nextMacroScope_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_ngen_1650_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_auxDeclNGen_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_traceState_1652_);
lean_ctor_set(v_reuseFailAlloc_1664_, 5, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_messages_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_infoState_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_snapshotTasks_1655_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_st_ref_set(v_a_1474_, v___x_1662_);
v_fileName_1614_ = v_fileName_1593_;
v_fileMap_1615_ = v_fileMap_1594_;
v_currRecDepth_1616_ = v_currRecDepth_1596_;
v_ref_1617_ = v_ref_1597_;
v_currNamespace_1618_ = v_currNamespace_1598_;
v_openDecls_1619_ = v_openDecls_1599_;
v_initHeartbeats_1620_ = v_initHeartbeats_1600_;
v_maxHeartbeats_1621_ = v_maxHeartbeats_1601_;
v_quotContext_1622_ = v_quotContext_1602_;
v_currMacroScope_1623_ = v_currMacroScope_1603_;
v_cancelTk_x3f_1624_ = v_cancelTk_x3f_1604_;
v_suppressElabErrors_1625_ = v_suppressElabErrors_1605_;
v_inheritedTraceOptions_1626_ = v_inheritedTraceOptions_1606_;
v___y_1627_ = v_a_1474_;
goto v___jp_1613_;
}
}
}
else
{
v_fileName_1614_ = v_fileName_1593_;
v_fileMap_1615_ = v_fileMap_1594_;
v_currRecDepth_1616_ = v_currRecDepth_1596_;
v_ref_1617_ = v_ref_1597_;
v_currNamespace_1618_ = v_currNamespace_1598_;
v_openDecls_1619_ = v_openDecls_1599_;
v_initHeartbeats_1620_ = v_initHeartbeats_1600_;
v_maxHeartbeats_1621_ = v_maxHeartbeats_1601_;
v_quotContext_1622_ = v_quotContext_1602_;
v_currMacroScope_1623_ = v_currMacroScope_1603_;
v_cancelTk_x3f_1624_ = v_cancelTk_x3f_1604_;
v_suppressElabErrors_1625_ = v_suppressElabErrors_1605_;
v_inheritedTraceOptions_1626_ = v_inheritedTraceOptions_1606_;
v___y_1627_ = v_a_1474_;
goto v___jp_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* v_addSubgoalsMsg_1668_, lean_object* v_checkState_x3f_1669_, lean_object* v_e_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1680_; lean_object* v_res_1681_; 
v_addSubgoalsMsg_boxed_1680_ = lean_unbox(v_addSubgoalsMsg_1668_);
v_res_1681_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_boxed_1680_, v_checkState_x3f_1669_, v_e_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object* v_as_1682_, size_t v_sz_1683_, size_t v_i_1684_, lean_object* v_b_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1682_, v_sz_1683_, v_i_1684_, v_b_1685_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object* v_as_1696_, lean_object* v_sz_1697_, lean_object* v_i_1698_, lean_object* v_b_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
size_t v_sz_boxed_1709_; size_t v_i_boxed_1710_; lean_object* v_res_1711_; 
v_sz_boxed_1709_ = lean_unbox_usize(v_sz_1697_);
lean_dec(v_sz_1697_);
v_i_boxed_1710_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_res_1711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_1696_, v_sz_boxed_1709_, v_i_boxed_1710_, v_b_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v_as_1696_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1712_, lean_object* v_msgData_1713_, uint8_t v_severity_1714_, uint8_t v_isSilent_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___y_1722_; uint8_t v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1758_; lean_object* v___y_1759_; uint8_t v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; uint8_t v___y_1763_; uint8_t v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; uint8_t v___y_1787_; uint8_t v___y_1788_; uint8_t v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; uint8_t v___y_1799_; uint8_t v___y_1800_; uint8_t v___x_1805_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1811_; uint8_t v___y_1812_; uint8_t v___y_1813_; uint8_t v___y_1815_; uint8_t v___x_1830_; 
v___x_1805_ = 2;
v___x_1830_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1714_, v___x_1805_);
if (v___x_1830_ == 0)
{
v___y_1815_ = v___x_1830_;
goto v___jp_1814_;
}
else
{
uint8_t v___x_1831_; 
lean_inc_ref(v_msgData_1713_);
v___x_1831_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1713_);
v___y_1815_ = v___x_1831_;
goto v___jp_1814_;
}
v___jp_1721_:
{
lean_object* v___x_1731_; lean_object* v_currNamespace_1732_; lean_object* v_openDecls_1733_; lean_object* v_env_1734_; lean_object* v_nextMacroScope_1735_; lean_object* v_ngen_1736_; lean_object* v_auxDeclNGen_1737_; lean_object* v_traceState_1738_; lean_object* v_cache_1739_; lean_object* v_messages_1740_; lean_object* v_infoState_1741_; lean_object* v_snapshotTasks_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1756_; 
v___x_1731_ = lean_st_ref_take(v___y_1730_);
v_currNamespace_1732_ = lean_ctor_get(v___y_1729_, 6);
v_openDecls_1733_ = lean_ctor_get(v___y_1729_, 7);
v_env_1734_ = lean_ctor_get(v___x_1731_, 0);
v_nextMacroScope_1735_ = lean_ctor_get(v___x_1731_, 1);
v_ngen_1736_ = lean_ctor_get(v___x_1731_, 2);
v_auxDeclNGen_1737_ = lean_ctor_get(v___x_1731_, 3);
v_traceState_1738_ = lean_ctor_get(v___x_1731_, 4);
v_cache_1739_ = lean_ctor_get(v___x_1731_, 5);
v_messages_1740_ = lean_ctor_get(v___x_1731_, 6);
v_infoState_1741_ = lean_ctor_get(v___x_1731_, 7);
v_snapshotTasks_1742_ = lean_ctor_get(v___x_1731_, 8);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1744_ = v___x_1731_;
v_isShared_1745_ = v_isSharedCheck_1756_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snapshotTasks_1742_);
lean_inc(v_infoState_1741_);
lean_inc(v_messages_1740_);
lean_inc(v_cache_1739_);
lean_inc(v_traceState_1738_);
lean_inc(v_auxDeclNGen_1737_);
lean_inc(v_ngen_1736_);
lean_inc(v_nextMacroScope_1735_);
lean_inc(v_env_1734_);
lean_dec(v___x_1731_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1756_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_inc(v_openDecls_1733_);
lean_inc(v_currNamespace_1732_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_currNamespace_1732_);
lean_ctor_set(v___x_1746_, 1, v_openDecls_1733_);
v___x_1747_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___y_1728_);
lean_inc_ref(v___y_1724_);
lean_inc_ref(v___y_1722_);
v___x_1748_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1748_, 0, v___y_1722_);
lean_ctor_set(v___x_1748_, 1, v___y_1726_);
lean_ctor_set(v___x_1748_, 2, v___y_1725_);
lean_ctor_set(v___x_1748_, 3, v___y_1724_);
lean_ctor_set(v___x_1748_, 4, v___x_1747_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*5, v___y_1727_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*5 + 1, v___y_1723_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*5 + 2, v_isSilent_1715_);
v___x_1749_ = l_Lean_MessageLog_add(v___x_1748_, v_messages_1740_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 6, v___x_1749_);
v___x_1751_ = v___x_1744_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_env_1734_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_nextMacroScope_1735_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_ngen_1736_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_auxDeclNGen_1737_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_traceState_1738_);
lean_ctor_set(v_reuseFailAlloc_1755_, 5, v_cache_1739_);
lean_ctor_set(v_reuseFailAlloc_1755_, 6, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1755_, 7, v_infoState_1741_);
lean_ctor_set(v_reuseFailAlloc_1755_, 8, v_snapshotTasks_1742_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_st_ref_set(v___y_1730_, v___x_1751_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
v___jp_1757_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1781_; 
v___x_1766_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1713_);
v___x_1767_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1766_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc_ref_n(v___y_1761_, 2);
v___x_1772_ = l_Lean_FileMap_toPosition(v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
v___x_1773_ = l_Lean_FileMap_toPosition(v___y_1761_, v___y_1765_);
lean_dec(v___y_1765_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_1763_ == 0)
{
lean_del_object(v___x_1770_);
lean_dec_ref(v___y_1758_);
v___y_1722_ = v___y_1759_;
v___y_1723_ = v___y_1760_;
v___y_1724_ = v___x_1775_;
v___y_1725_ = v___x_1774_;
v___y_1726_ = v___x_1772_;
v___y_1727_ = v___y_1764_;
v___y_1728_ = v_a_1768_;
v___y_1729_ = v___y_1718_;
v___y_1730_ = v___y_1719_;
goto v___jp_1721_;
}
else
{
uint8_t v___x_1776_; 
lean_inc(v_a_1768_);
v___x_1776_ = l_Lean_MessageData_hasTag(v___y_1758_, v_a_1768_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1772_);
lean_dec(v_a_1768_);
v___x_1777_ = lean_box(0);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1777_);
v___x_1779_ = v___x_1770_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
else
{
lean_del_object(v___x_1770_);
v___y_1722_ = v___y_1759_;
v___y_1723_ = v___y_1760_;
v___y_1724_ = v___x_1775_;
v___y_1725_ = v___x_1774_;
v___y_1726_ = v___x_1772_;
v___y_1727_ = v___y_1764_;
v___y_1728_ = v_a_1768_;
v___y_1729_ = v___y_1718_;
v___y_1730_ = v___y_1719_;
goto v___jp_1721_;
}
}
}
}
v___jp_1782_:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Syntax_getTailPos_x3f(v___y_1785_, v___y_1788_);
lean_dec(v___y_1785_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_inc(v___y_1790_);
v___y_1758_ = v___y_1783_;
v___y_1759_ = v___y_1784_;
v___y_1760_ = v___y_1787_;
v___y_1761_ = v___y_1786_;
v___y_1762_ = v___y_1790_;
v___y_1763_ = v___y_1789_;
v___y_1764_ = v___y_1788_;
v___y_1765_ = v___y_1790_;
goto v___jp_1757_;
}
else
{
lean_object* v_val_1792_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref(v___x_1791_);
v___y_1758_ = v___y_1783_;
v___y_1759_ = v___y_1784_;
v___y_1760_ = v___y_1787_;
v___y_1761_ = v___y_1786_;
v___y_1762_ = v___y_1790_;
v___y_1763_ = v___y_1789_;
v___y_1764_ = v___y_1788_;
v___y_1765_ = v_val_1792_;
goto v___jp_1757_;
}
}
v___jp_1793_:
{
lean_object* v_ref_1801_; lean_object* v___x_1802_; 
v_ref_1801_ = l_Lean_replaceRef(v_ref_1712_, v___y_1797_);
v___x_1802_ = l_Lean_Syntax_getPos_x3f(v_ref_1801_, v___y_1799_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___y_1783_ = v___y_1794_;
v___y_1784_ = v___y_1795_;
v___y_1785_ = v_ref_1801_;
v___y_1786_ = v___y_1796_;
v___y_1787_ = v___y_1800_;
v___y_1788_ = v___y_1799_;
v___y_1789_ = v___y_1798_;
v___y_1790_ = v___x_1803_;
goto v___jp_1782_;
}
else
{
lean_object* v_val_1804_; 
v_val_1804_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_val_1804_);
lean_dec_ref(v___x_1802_);
v___y_1783_ = v___y_1794_;
v___y_1784_ = v___y_1795_;
v___y_1785_ = v_ref_1801_;
v___y_1786_ = v___y_1796_;
v___y_1787_ = v___y_1800_;
v___y_1788_ = v___y_1799_;
v___y_1789_ = v___y_1798_;
v___y_1790_ = v_val_1804_;
goto v___jp_1782_;
}
}
v___jp_1806_:
{
if (v___y_1813_ == 0)
{
v___y_1794_ = v___y_1809_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1808_;
v___y_1797_ = v___y_1810_;
v___y_1798_ = v___y_1811_;
v___y_1799_ = v___y_1812_;
v___y_1800_ = v_severity_1714_;
goto v___jp_1793_;
}
else
{
v___y_1794_ = v___y_1809_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1808_;
v___y_1797_ = v___y_1810_;
v___y_1798_ = v___y_1811_;
v___y_1799_ = v___y_1812_;
v___y_1800_ = v___x_1805_;
goto v___jp_1793_;
}
}
v___jp_1814_:
{
if (v___y_1815_ == 0)
{
lean_object* v_fileName_1816_; lean_object* v_fileMap_1817_; lean_object* v_options_1818_; lean_object* v_ref_1819_; uint8_t v_suppressElabErrors_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___f_1823_; uint8_t v___x_1824_; uint8_t v___x_1825_; 
v_fileName_1816_ = lean_ctor_get(v___y_1718_, 0);
v_fileMap_1817_ = lean_ctor_get(v___y_1718_, 1);
v_options_1818_ = lean_ctor_get(v___y_1718_, 2);
v_ref_1819_ = lean_ctor_get(v___y_1718_, 5);
v_suppressElabErrors_1820_ = lean_ctor_get_uint8(v___y_1718_, sizeof(void*)*14 + 1);
v___x_1821_ = lean_box(v___y_1815_);
v___x_1822_ = lean_box(v_suppressElabErrors_1820_);
v___f_1823_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1823_, 0, v___x_1821_);
lean_closure_set(v___f_1823_, 1, v___x_1822_);
v___x_1824_ = 1;
v___x_1825_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1714_, v___x_1824_);
if (v___x_1825_ == 0)
{
v___y_1807_ = v_fileName_1816_;
v___y_1808_ = v_fileMap_1817_;
v___y_1809_ = v___f_1823_;
v___y_1810_ = v_ref_1819_;
v___y_1811_ = v_suppressElabErrors_1820_;
v___y_1812_ = v___y_1815_;
v___y_1813_ = v___x_1825_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = l_Lean_warningAsError;
v___x_1827_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1818_, v___x_1826_);
v___y_1807_ = v_fileName_1816_;
v___y_1808_ = v_fileMap_1817_;
v___y_1809_ = v___f_1823_;
v___y_1810_ = v_ref_1819_;
v___y_1811_ = v_suppressElabErrors_1820_;
v___y_1812_ = v___y_1815_;
v___y_1813_ = v___x_1827_;
goto v___jp_1806_;
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_msgData_1713_);
v___x_1828_ = lean_box(0);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1832_, lean_object* v_msgData_1833_, lean_object* v_severity_1834_, lean_object* v_isSilent_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_severity_boxed_1841_; uint8_t v_isSilent_boxed_1842_; lean_object* v_res_1843_; 
v_severity_boxed_1841_ = lean_unbox(v_severity_1834_);
v_isSilent_boxed_1842_ = lean_unbox(v_isSilent_1835_);
v_res_1843_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1832_, v_msgData_1833_, v_severity_boxed_1841_, v_isSilent_boxed_1842_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v_ref_1832_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(lean_object* v_msgData_1844_, uint8_t v_severity_1845_, uint8_t v_isSilent_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_ref_1856_; lean_object* v___x_1857_; 
v_ref_1856_ = lean_ctor_get(v___y_1853_, 5);
v___x_1857_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1856_, v_msgData_1844_, v_severity_1845_, v_isSilent_1846_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(lean_object* v_msgData_1858_, lean_object* v_severity_1859_, lean_object* v_isSilent_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v_severity_boxed_1870_; uint8_t v_isSilent_boxed_1871_; lean_object* v_res_1872_; 
v_severity_boxed_1870_ = lean_unbox(v_severity_1859_);
v_isSilent_boxed_1871_ = lean_unbox(v_isSilent_1860_);
v_res_1872_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1858_, v_severity_boxed_1870_, v_isSilent_boxed_1871_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object* v_msgData_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = 0;
v___x_1884_ = 0;
v___x_1885_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1873_, v___x_1883_, v___x_1884_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object* v_msgData_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_msgData_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* v_ref_1898_, lean_object* v_e_1899_, lean_object* v_origSpan_x3f_1900_, uint8_t v_addSubgoalsMsg_1901_, lean_object* v_codeActionPrefix_x3f_1902_, lean_object* v_checkState_x3f_1903_, uint8_t v_tacticErrorAsInfo_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_1901_, v_checkState_x3f_1903_, v_e_1899_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v_val_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; 
v_val_1916_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_val_1916_);
lean_dec_ref(v_a_1915_);
v___x_1917_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_1918_ = 4;
v___x_1919_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_1898_, v_val_1916_, v_origSpan_x3f_1900_, v___x_1917_, v_codeActionPrefix_x3f_1902_, v___x_1918_, v_a_1911_, v_a_1912_);
return v___x_1919_;
}
else
{
lean_dec(v_codeActionPrefix_x3f_1902_);
lean_dec(v_origSpan_x3f_1900_);
lean_dec(v_ref_1898_);
if (v_tacticErrorAsInfo_1904_ == 0)
{
lean_object* v_val_1920_; lean_object* v___x_1921_; 
v_val_1920_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_val_1920_);
lean_dec_ref(v_a_1915_);
v___x_1921_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_1920_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1921_;
}
else
{
lean_object* v_val_1922_; lean_object* v___x_1923_; 
v_val_1922_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_val_1922_);
lean_dec_ref(v_a_1915_);
v___x_1923_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_val_1922_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_codeActionPrefix_x3f_1902_);
lean_dec(v_origSpan_x3f_1900_);
lean_dec(v_ref_1898_);
v_a_1924_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1914_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1914_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* v_ref_1932_, lean_object* v_e_1933_, lean_object* v_origSpan_x3f_1934_, lean_object* v_addSubgoalsMsg_1935_, lean_object* v_codeActionPrefix_x3f_1936_, lean_object* v_checkState_x3f_1937_, lean_object* v_tacticErrorAsInfo_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1948_; uint8_t v_tacticErrorAsInfo_boxed_1949_; lean_object* v_res_1950_; 
v_addSubgoalsMsg_boxed_1948_ = lean_unbox(v_addSubgoalsMsg_1935_);
v_tacticErrorAsInfo_boxed_1949_ = lean_unbox(v_tacticErrorAsInfo_1938_);
v_res_1950_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_ref_1932_, v_e_1933_, v_origSpan_x3f_1934_, v_addSubgoalsMsg_boxed_1948_, v_codeActionPrefix_x3f_1936_, v_checkState_x3f_1937_, v_tacticErrorAsInfo_boxed_1949_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(lean_object* v_ref_1951_, lean_object* v_msgData_1952_, uint8_t v_severity_1953_, uint8_t v_isSilent_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1951_, v_msgData_1952_, v_severity_1953_, v_isSilent_1954_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1965_, lean_object* v_msgData_1966_, lean_object* v_severity_1967_, lean_object* v_isSilent_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_severity_boxed_1978_; uint8_t v_isSilent_boxed_1979_; lean_object* v_res_1980_; 
v_severity_boxed_1978_ = lean_unbox(v_severity_1967_);
v_isSilent_boxed_1979_ = lean_unbox(v_isSilent_1968_);
v_res_1980_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_1965_, v_msgData_1966_, v_severity_boxed_1978_, v_isSilent_boxed_1979_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_ref_1965_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(uint8_t v_tacticErrorAsInfo_1981_, lean_object* v_as_1982_, size_t v_sz_1983_, size_t v_i_1984_, lean_object* v_b_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_a_1992_; uint8_t v___x_1996_; 
v___x_1996_ = lean_usize_dec_lt(v_i_1984_, v_sz_1983_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_b_1985_);
return v___x_1997_;
}
else
{
lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2024_; 
v_fst_1998_ = lean_ctor_get(v_b_1985_, 0);
v_snd_1999_ = lean_ctor_get(v_b_1985_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_b_1985_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2001_ = v_b_1985_;
v_isShared_2002_ = v_isSharedCheck_2024_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_inc(v_fst_1998_);
lean_dec(v_b_1985_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2024_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_array_uget_borrowed(v_as_1982_, v_i_1984_);
if (lean_obj_tag(v_a_2003_) == 0)
{
lean_object* v_val_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v_val_2004_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_val_2004_);
v___x_2005_ = lean_array_push(v_fst_1998_, v_val_2004_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2005_);
v___x_2007_ = v___x_2001_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_snd_1999_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v_a_1992_ = v___x_2007_;
goto v___jp_1991_;
}
}
else
{
lean_object* v_val_2009_; 
v_val_2009_ = lean_ctor_get(v_a_2003_, 0);
if (v_tacticErrorAsInfo_1981_ == 0)
{
lean_object* v___x_2015_; 
lean_inc(v_val_2009_);
v___x_2015_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_2009_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref(v___x_2015_);
goto v___jp_2010_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_del_object(v___x_2001_);
lean_dec(v_snd_1999_);
lean_dec(v_fst_1998_);
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
goto v___jp_2010_;
}
v___jp_2010_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
lean_inc(v_val_2009_);
v___x_2011_ = lean_array_push(v_snd_1999_, v_val_2009_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2011_);
v___x_2013_ = v___x_2001_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_fst_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
v_a_1992_ = v___x_2013_;
goto v___jp_1991_;
}
}
}
}
}
v___jp_1991_:
{
size_t v___x_1993_; size_t v___x_1994_; 
v___x_1993_ = ((size_t)1ULL);
v___x_1994_ = lean_usize_add(v_i_1984_, v___x_1993_);
v_i_1984_ = v___x_1994_;
v_b_1985_ = v_a_1992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(lean_object* v_tacticErrorAsInfo_2025_, lean_object* v_as_2026_, lean_object* v_sz_2027_, lean_object* v_i_2028_, lean_object* v_b_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2035_; size_t v_sz_boxed_2036_; size_t v_i_boxed_2037_; lean_object* v_res_2038_; 
v_tacticErrorAsInfo_boxed_2035_ = lean_unbox(v_tacticErrorAsInfo_2025_);
v_sz_boxed_2036_ = lean_unbox_usize(v_sz_2027_);
lean_dec(v_sz_2027_);
v_i_boxed_2037_ = lean_unbox_usize(v_i_2028_);
lean_dec(v_i_2028_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_boxed_2035_, v_as_2026_, v_sz_boxed_2036_, v_i_boxed_2037_, v_b_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec_ref(v_as_2026_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t v_addSubgoalsMsg_2039_, lean_object* v_checkState_x3f_2040_, size_t v_sz_2041_, size_t v_i_2042_, lean_object* v_bs_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_usize_dec_lt(v_i_2042_, v_sz_2041_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
lean_dec(v_checkState_x3f_2040_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_bs_2043_);
return v___x_2054_;
}
else
{
lean_object* v_v_2055_; lean_object* v___x_2056_; 
v_v_2055_ = lean_array_uget_borrowed(v_bs_2043_, v_i_2042_);
lean_inc(v_v_2055_);
lean_inc(v_checkState_x3f_2040_);
v___x_2056_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_2039_, v_checkState_x3f_2040_, v_v_2055_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; lean_object* v_bs_x27_2059_; size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = lean_unsigned_to_nat(0u);
v_bs_x27_2059_ = lean_array_uset(v_bs_2043_, v_i_2042_, v___x_2058_);
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2042_, v___x_2060_);
v___x_2062_ = lean_array_uset(v_bs_x27_2059_, v_i_2042_, v_a_2057_);
v_i_2042_ = v___x_2061_;
v_bs_2043_ = v___x_2062_;
goto _start;
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_bs_2043_);
lean_dec(v_checkState_x3f_2040_);
v_a_2064_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2056_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2056_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object* v_addSubgoalsMsg_2072_, lean_object* v_checkState_x3f_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_bs_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2086_; size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_addSubgoalsMsg_boxed_2086_ = lean_unbox(v_addSubgoalsMsg_2072_);
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_boxed_2086_, v_checkState_x3f_2073_, v_sz_boxed_2087_, v_i_boxed_2088_, v_bs_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(lean_object* v_as_2090_, size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_b_2093_);
return v___x_2104_;
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_array_uget_borrowed(v_as_2090_, v_i_2092_);
lean_inc(v_a_2105_);
v___x_2106_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_a_2105_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; 
lean_dec_ref(v___x_2106_);
v___x_2107_ = lean_box(0);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2092_, v___x_2108_);
v_i_2092_ = v___x_2109_;
v_b_2093_ = v___x_2107_;
goto _start;
}
else
{
return v___x_2106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(lean_object* v_as_2111_, lean_object* v_sz_2112_, lean_object* v_i_2113_, lean_object* v_b_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
size_t v_sz_boxed_2124_; size_t v_i_boxed_2125_; lean_object* v_res_2126_; 
v_sz_boxed_2124_ = lean_unbox_usize(v_sz_2112_);
lean_dec(v_sz_2112_);
v_i_boxed_2125_ = lean_unbox_usize(v_i_2113_);
lean_dec(v_i_2113_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_2111_, v_sz_boxed_2124_, v_i_boxed_2125_, v_b_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec_ref(v_as_2111_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* v_ref_2132_, lean_object* v_es_2133_, lean_object* v_origSpan_x3f_2134_, uint8_t v_addSubgoalsMsg_2135_, lean_object* v_codeActionPrefix_x3f_2136_, lean_object* v_checkState_x3f_2137_, uint8_t v_tacticErrorAsInfo_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
size_t v_sz_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v_sz_2148_ = lean_array_size(v_es_2133_);
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_2135_, v_checkState_x3f_2137_, v_sz_2148_, v___x_2149_, v_es_2133_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; size_t v_sz_2153_; lean_object* v___x_2154_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1));
v_sz_2153_ = lean_array_size(v_a_2151_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2138_, v_a_2151_, v_sz_2153_, v___x_2149_, v___x_2152_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2151_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_fst_2156_; lean_object* v_snd_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v_fst_2156_ = lean_ctor_get(v_a_2155_, 0);
lean_inc(v_fst_2156_);
v_snd_2157_ = lean_ctor_get(v_a_2155_, 1);
lean_inc(v_snd_2157_);
lean_dec(v_a_2155_);
v___x_2158_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2));
v___x_2159_ = 4;
v___x_2160_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2132_, v_fst_2156_, v_origSpan_x3f_2134_, v___x_2158_, v_codeActionPrefix_x3f_2136_, v___x_2159_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2161_; size_t v_sz_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v___x_2160_);
v___x_2161_ = lean_box(0);
v_sz_2162_ = lean_array_size(v_snd_2157_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_snd_2157_, v_sz_2162_, v___x_2149_, v___x_2161_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_snd_2157_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2163_, 0);
lean_dec(v_unused_2171_);
v___x_2165_ = v___x_2163_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_dec(v___x_2163_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2161_);
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2161_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
return v___x_2163_;
}
}
else
{
lean_dec(v_snd_2157_);
return v___x_2160_;
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_codeActionPrefix_x3f_2136_);
lean_dec(v_origSpan_x3f_2134_);
lean_dec(v_ref_2132_);
v_a_2172_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2154_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2154_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_codeActionPrefix_x3f_2136_);
lean_dec(v_origSpan_x3f_2134_);
lean_dec(v_ref_2132_);
v_a_2180_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2150_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2150_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* v_ref_2188_, lean_object* v_es_2189_, lean_object* v_origSpan_x3f_2190_, lean_object* v_addSubgoalsMsg_2191_, lean_object* v_codeActionPrefix_x3f_2192_, lean_object* v_checkState_x3f_2193_, lean_object* v_tacticErrorAsInfo_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2204_; uint8_t v_tacticErrorAsInfo_boxed_2205_; lean_object* v_res_2206_; 
v_addSubgoalsMsg_boxed_2204_ = lean_unbox(v_addSubgoalsMsg_2191_);
v_tacticErrorAsInfo_boxed_2205_ = lean_unbox(v_tacticErrorAsInfo_2194_);
v_res_2206_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(v_ref_2188_, v_es_2189_, v_origSpan_x3f_2190_, v_addSubgoalsMsg_boxed_2204_, v_codeActionPrefix_x3f_2192_, v_checkState_x3f_2193_, v_tacticErrorAsInfo_boxed_2205_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t v_tacticErrorAsInfo_2207_, lean_object* v_as_2208_, size_t v_sz_2209_, size_t v_i_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2207_, v_as_2208_, v_sz_2209_, v_i_2210_, v_b_2211_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object* v_tacticErrorAsInfo_2222_, lean_object* v_as_2223_, lean_object* v_sz_2224_, lean_object* v_i_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2236_; size_t v_sz_boxed_2237_; size_t v_i_boxed_2238_; lean_object* v_res_2239_; 
v_tacticErrorAsInfo_boxed_2236_ = lean_unbox(v_tacticErrorAsInfo_2222_);
v_sz_boxed_2237_ = lean_unbox_usize(v_sz_2224_);
lean_dec(v_sz_2224_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_boxed_2236_, v_as_2223_, v_sz_boxed_2237_, v_i_boxed_2238_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v_as_2223_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* v_ref_2240_, lean_object* v_e_2241_, lean_object* v_origSpan_x3f_2242_, lean_object* v_header_2243_, lean_object* v_codeActionPrefix_x3f_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_2241_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref(v___x_2250_);
v___x_2252_ = 4;
v___x_2253_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2240_, v_a_2251_, v_origSpan_x3f_2242_, v_header_2243_, v_codeActionPrefix_x3f_2244_, v___x_2252_, v_a_2247_, v_a_2248_);
return v___x_2253_;
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_codeActionPrefix_x3f_2244_);
lean_dec_ref(v_header_2243_);
lean_dec(v_origSpan_x3f_2242_);
lean_dec(v_ref_2240_);
v_a_2254_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2250_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2250_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object* v_ref_2262_, lean_object* v_e_2263_, lean_object* v_origSpan_x3f_2264_, lean_object* v_header_2265_, lean_object* v_codeActionPrefix_x3f_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_ref_2262_, v_e_2263_, v_origSpan_x3f_2264_, v_header_2265_, v_codeActionPrefix_x3f_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2274_, v_sz_2273_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_bs_2275_);
return v___x_2282_;
}
else
{
lean_object* v_v_2283_; lean_object* v___x_2284_; 
v_v_2283_ = lean_array_uget_borrowed(v_bs_2275_, v_i_2274_);
lean_inc(v_v_2283_);
v___x_2284_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_v_2283_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; lean_object* v_bs_x27_2287_; size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = lean_unsigned_to_nat(0u);
v_bs_x27_2287_ = lean_array_uset(v_bs_2275_, v_i_2274_, v___x_2286_);
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_add(v_i_2274_, v___x_2288_);
v___x_2290_ = lean_array_uset(v_bs_x27_2287_, v_i_2274_, v_a_2285_);
v_i_2274_ = v___x_2289_;
v_bs_2275_ = v___x_2290_;
goto _start;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_bs_2275_);
v_a_2292_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2284_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2284_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object* v_sz_2300_, lean_object* v_i_2301_, lean_object* v_bs_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
size_t v_sz_boxed_2308_; size_t v_i_boxed_2309_; lean_object* v_res_2310_; 
v_sz_boxed_2308_ = lean_unbox_usize(v_sz_2300_);
lean_dec(v_sz_2300_);
v_i_boxed_2309_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_boxed_2308_, v_i_boxed_2309_, v_bs_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* v_ref_2311_, lean_object* v_es_2312_, lean_object* v_origSpan_x3f_2313_, lean_object* v_header_2314_, lean_object* v_codeActionPrefix_x3f_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
size_t v_sz_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v_sz_2321_ = lean_array_size(v_es_2312_);
v___x_2322_ = ((size_t)0ULL);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_2321_, v___x_2322_, v_es_2312_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = 4;
v___x_2326_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2311_, v_a_2324_, v_origSpan_x3f_2313_, v_header_2314_, v_codeActionPrefix_x3f_2315_, v___x_2325_, v_a_2318_, v_a_2319_);
return v___x_2326_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_codeActionPrefix_x3f_2315_);
lean_dec_ref(v_header_2314_);
lean_dec(v_origSpan_x3f_2313_);
lean_dec(v_ref_2311_);
v_a_2327_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2323_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2323_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object* v_ref_2335_, lean_object* v_es_2336_, lean_object* v_origSpan_x3f_2337_, lean_object* v_header_2338_, lean_object* v_codeActionPrefix_x3f_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(v_ref_2335_, v_es_2336_, v_origSpan_x3f_2337_, v_header_2338_, v_codeActionPrefix_x3f_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
return v_res_2345_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Array_mkArray0(lean_box(0));
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_2410_ = l_String_toRawSubstring_x27(v___x_2409_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object* v_e_2556_, lean_object* v_t_x3f_2557_, uint8_t v_a_2558_, lean_object* v_h_x3f_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_fst_2566_; lean_object* v_snd_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___x_2582_; 
lean_inc_ref(v_e_2556_);
v___x_2582_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_2556_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___y_2585_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
if (lean_obj_tag(v_t_x3f_2557_) == 1)
{
lean_object* v_val_2613_; lean_object* v___x_2614_; 
v_val_2613_ = lean_ctor_get(v_t_x3f_2557_, 0);
lean_inc_n(v_val_2613_, 2);
lean_dec_ref(v_t_x3f_2557_);
v___x_2614_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_val_2613_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___y_2617_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
if (v_a_2558_ == 0)
{
if (lean_obj_tag(v_h_x3f_2559_) == 0)
{
lean_object* v___x_2654_; 
v___x_2654_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2617_ = v___x_2654_;
goto v___jp_2616_;
}
else
{
lean_object* v_val_2655_; 
v_val_2655_ = lean_ctor_get(v_h_x3f_2559_, 0);
lean_inc(v_val_2655_);
lean_dec_ref(v_h_x3f_2559_);
v___y_2617_ = v_val_2655_;
goto v___jp_2616_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2559_) == 0)
{
lean_object* v_ref_2656_; lean_object* v_quotContext_2657_; lean_object* v_currMacroScope_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_ref_2656_ = lean_ctor_get(v___y_2562_, 5);
v_quotContext_2657_ = lean_ctor_get(v___y_2562_, 10);
v_currMacroScope_2658_ = lean_ctor_get(v___y_2562_, 11);
v___x_2659_ = 0;
v___x_2660_ = l_Lean_SourceInfo_fromRef(v_ref_2656_, v___x_2659_);
v___x_2661_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2662_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2660_, 12);
v___x_2663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2660_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2666_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2660_);
lean_ctor_set(v___x_2667_, 1, v___x_2665_);
lean_ctor_set(v___x_2667_, 2, v___x_2666_);
lean_inc_ref(v___x_2667_);
v___x_2668_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2664_, v___x_2667_);
v___x_2669_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2670_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2671_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2672_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2673_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2674_ = lean_box(0);
lean_inc(v_currMacroScope_2658_);
lean_inc(v_quotContext_2657_);
v___x_2675_ = l_Lean_addMacroScope(v_quotContext_2657_, v___x_2674_, v_currMacroScope_2658_);
v___x_2676_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2677_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2660_);
lean_ctor_set(v___x_2677_, 1, v___x_2673_);
lean_ctor_set(v___x_2677_, 2, v___x_2675_);
lean_ctor_set(v___x_2677_, 3, v___x_2676_);
v___x_2678_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2672_, v___x_2677_);
v___x_2679_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2671_, v___x_2678_);
v___x_2680_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2681_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2660_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_Syntax_node2(v___x_2660_, v___x_2680_, v___x_2682_, v_a_2615_);
v___x_2684_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2665_, v___x_2683_);
v___x_2685_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2660_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node5(v___x_2660_, v___x_2670_, v___x_2679_, v___x_2667_, v___x_2684_, v___x_2686_, v_a_2583_);
v___x_2688_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2669_, v___x_2687_);
v___x_2689_ = l_Lean_Syntax_node3(v___x_2660_, v___x_2661_, v___x_2663_, v___x_2668_, v___x_2688_);
v___x_2690_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81);
v___x_2691_ = l_Lean_MessageData_ofExpr(v_val_2613_);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l_Lean_MessageData_ofExpr(v_e_2556_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v_fst_2566_ = v___x_2689_;
v_snd_2567_ = v___x_2696_;
v___y_2568_ = v___y_2560_;
v___y_2569_ = v___y_2561_;
v___y_2570_ = v___y_2562_;
v___y_2571_ = v___y_2563_;
goto v___jp_2565_;
}
else
{
lean_object* v_val_2697_; lean_object* v_ref_2698_; uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_val_2697_ = lean_ctor_get(v_h_x3f_2559_, 0);
lean_inc_n(v_val_2697_, 2);
lean_dec_ref(v_h_x3f_2559_);
v_ref_2698_ = lean_ctor_get(v___y_2562_, 5);
v___x_2699_ = 0;
v___x_2700_ = l_Lean_SourceInfo_fromRef(v_ref_2698_, v___x_2699_);
v___x_2701_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2702_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2700_, 10);
v___x_2703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2700_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2706_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2700_);
lean_ctor_set(v___x_2707_, 1, v___x_2705_);
lean_ctor_set(v___x_2707_, 2, v___x_2706_);
lean_inc_ref(v___x_2707_);
v___x_2708_ = l_Lean_Syntax_node1(v___x_2700_, v___x_2704_, v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2710_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2711_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2712_ = lean_mk_syntax_ident(v_val_2697_);
v___x_2713_ = l_Lean_Syntax_node1(v___x_2700_, v___x_2711_, v___x_2712_);
v___x_2714_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2715_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2700_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_Syntax_node2(v___x_2700_, v___x_2714_, v___x_2716_, v_a_2615_);
v___x_2718_ = l_Lean_Syntax_node1(v___x_2700_, v___x_2705_, v___x_2717_);
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2700_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_Syntax_node5(v___x_2700_, v___x_2710_, v___x_2713_, v___x_2707_, v___x_2718_, v___x_2720_, v_a_2583_);
v___x_2722_ = l_Lean_Syntax_node1(v___x_2700_, v___x_2709_, v___x_2721_);
v___x_2723_ = l_Lean_Syntax_node3(v___x_2700_, v___x_2701_, v___x_2703_, v___x_2708_, v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2725_ = l_Lean_MessageData_ofName(v_val_2697_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = l_Lean_MessageData_ofExpr(v_val_2613_);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = l_Lean_MessageData_ofExpr(v_e_2556_);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v_fst_2566_ = v___x_2723_;
v_snd_2567_ = v___x_2734_;
v___y_2568_ = v___y_2560_;
v___y_2569_ = v___y_2561_;
v___y_2570_ = v___y_2562_;
v___y_2571_ = v___y_2563_;
goto v___jp_2565_;
}
}
v___jp_2616_:
{
lean_object* v_ref_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_ref_2618_ = lean_ctor_get(v___y_2562_, 5);
v___x_2619_ = l_Lean_SourceInfo_fromRef(v_ref_2618_, v_a_2558_);
v___x_2620_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2621_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2619_, 10);
v___x_2622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2619_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2625_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2619_);
lean_ctor_set(v___x_2626_, 1, v___x_2624_);
lean_ctor_set(v___x_2626_, 2, v___x_2625_);
lean_inc_ref(v___x_2626_);
v___x_2627_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2623_, v___x_2626_);
v___x_2628_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2629_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2630_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2617_);
v___x_2631_ = lean_mk_syntax_ident(v___y_2617_);
v___x_2632_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2630_, v___x_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2634_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2619_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_Syntax_node2(v___x_2619_, v___x_2633_, v___x_2635_, v_a_2615_);
v___x_2637_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2624_, v___x_2636_);
v___x_2638_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2619_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = l_Lean_Syntax_node5(v___x_2619_, v___x_2629_, v___x_2632_, v___x_2626_, v___x_2637_, v___x_2639_, v_a_2583_);
v___x_2641_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2628_, v___x_2640_);
v___x_2642_ = l_Lean_Syntax_node3(v___x_2619_, v___x_2620_, v___x_2622_, v___x_2627_, v___x_2641_);
v___x_2643_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2644_ = l_Lean_MessageData_ofName(v___y_2617_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_MessageData_ofExpr(v_val_2613_);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2649_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_MessageData_ofExpr(v_e_2556_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v_fst_2566_ = v___x_2642_;
v_snd_2567_ = v___x_2653_;
v___y_2568_ = v___y_2560_;
v___y_2569_ = v___y_2561_;
v___y_2570_ = v___y_2562_;
v___y_2571_ = v___y_2563_;
goto v___jp_2565_;
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_val_2613_);
lean_dec(v_a_2583_);
lean_dec_ref(v___y_2562_);
lean_dec(v_h_x3f_2559_);
lean_dec_ref(v_e_2556_);
v_a_2735_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2614_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2614_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_dec(v_t_x3f_2557_);
if (v_a_2558_ == 0)
{
if (lean_obj_tag(v_h_x3f_2559_) == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2585_ = v___x_2743_;
goto v___jp_2584_;
}
else
{
lean_object* v_val_2744_; 
v_val_2744_ = lean_ctor_get(v_h_x3f_2559_, 0);
lean_inc(v_val_2744_);
lean_dec_ref(v_h_x3f_2559_);
v___y_2585_ = v_val_2744_;
goto v___jp_2584_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2559_) == 0)
{
lean_object* v_ref_2745_; lean_object* v_quotContext_2746_; lean_object* v_currMacroScope_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_ref_2745_ = lean_ctor_get(v___y_2562_, 5);
v_quotContext_2746_ = lean_ctor_get(v___y_2562_, 10);
v_currMacroScope_2747_ = lean_ctor_get(v___y_2562_, 11);
v___x_2748_ = 0;
v___x_2749_ = l_Lean_SourceInfo_fromRef(v_ref_2745_, v___x_2748_);
v___x_2750_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2751_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2749_, 9);
v___x_2752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2749_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2755_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2749_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
lean_inc_ref_n(v___x_2756_, 2);
v___x_2757_ = l_Lean_Syntax_node1(v___x_2749_, v___x_2753_, v___x_2756_);
v___x_2758_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2759_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2760_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2761_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2762_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2763_ = lean_box(0);
lean_inc(v_currMacroScope_2747_);
lean_inc(v_quotContext_2746_);
v___x_2764_ = l_Lean_addMacroScope(v_quotContext_2746_, v___x_2763_, v_currMacroScope_2747_);
v___x_2765_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2749_);
lean_ctor_set(v___x_2766_, 1, v___x_2762_);
lean_ctor_set(v___x_2766_, 2, v___x_2764_);
lean_ctor_set(v___x_2766_, 3, v___x_2765_);
v___x_2767_ = l_Lean_Syntax_node1(v___x_2749_, v___x_2761_, v___x_2766_);
v___x_2768_ = l_Lean_Syntax_node1(v___x_2749_, v___x_2760_, v___x_2767_);
v___x_2769_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2749_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = l_Lean_Syntax_node5(v___x_2749_, v___x_2759_, v___x_2768_, v___x_2756_, v___x_2756_, v___x_2770_, v_a_2583_);
v___x_2772_ = l_Lean_Syntax_node1(v___x_2749_, v___x_2758_, v___x_2771_);
v___x_2773_ = l_Lean_Syntax_node3(v___x_2749_, v___x_2750_, v___x_2752_, v___x_2757_, v___x_2772_);
v___x_2774_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85);
v___x_2775_ = l_Lean_MessageData_ofExpr(v_e_2556_);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v_fst_2566_ = v___x_2773_;
v_snd_2567_ = v___x_2776_;
v___y_2568_ = v___y_2560_;
v___y_2569_ = v___y_2561_;
v___y_2570_ = v___y_2562_;
v___y_2571_ = v___y_2563_;
goto v___jp_2565_;
}
else
{
lean_object* v_val_2777_; lean_object* v_ref_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_val_2777_ = lean_ctor_get(v_h_x3f_2559_, 0);
lean_inc_n(v_val_2777_, 2);
lean_dec_ref(v_h_x3f_2559_);
v_ref_2778_ = lean_ctor_get(v___y_2562_, 5);
v___x_2779_ = 0;
v___x_2780_ = l_Lean_SourceInfo_fromRef(v_ref_2778_, v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2782_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2780_, 7);
v___x_2783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2780_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2786_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2780_);
lean_ctor_set(v___x_2787_, 1, v___x_2785_);
lean_ctor_set(v___x_2787_, 2, v___x_2786_);
lean_inc_ref_n(v___x_2787_, 2);
v___x_2788_ = l_Lean_Syntax_node1(v___x_2780_, v___x_2784_, v___x_2787_);
v___x_2789_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2790_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2791_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2792_ = lean_mk_syntax_ident(v_val_2777_);
v___x_2793_ = l_Lean_Syntax_node1(v___x_2780_, v___x_2791_, v___x_2792_);
v___x_2794_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2780_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_Syntax_node5(v___x_2780_, v___x_2790_, v___x_2793_, v___x_2787_, v___x_2787_, v___x_2795_, v_a_2583_);
v___x_2797_ = l_Lean_Syntax_node1(v___x_2780_, v___x_2789_, v___x_2796_);
v___x_2798_ = l_Lean_Syntax_node3(v___x_2780_, v___x_2781_, v___x_2783_, v___x_2788_, v___x_2797_);
v___x_2799_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2800_ = l_Lean_MessageData_ofName(v_val_2777_);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = l_Lean_MessageData_ofExpr(v_e_2556_);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v_fst_2566_ = v___x_2798_;
v_snd_2567_ = v___x_2805_;
v___y_2568_ = v___y_2560_;
v___y_2569_ = v___y_2561_;
v___y_2570_ = v___y_2562_;
v___y_2571_ = v___y_2563_;
goto v___jp_2565_;
}
}
}
v___jp_2584_:
{
lean_object* v_ref_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_ref_2586_ = lean_ctor_get(v___y_2562_, 5);
v___x_2587_ = l_Lean_SourceInfo_fromRef(v_ref_2586_, v_a_2558_);
v___x_2588_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2589_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2587_, 7);
v___x_2590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2587_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2593_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2587_);
lean_ctor_set(v___x_2594_, 1, v___x_2592_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
lean_inc_ref_n(v___x_2594_, 2);
v___x_2595_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2591_, v___x_2594_);
v___x_2596_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2597_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2598_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2585_);
v___x_2599_ = lean_mk_syntax_ident(v___y_2585_);
v___x_2600_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2598_, v___x_2599_);
v___x_2601_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2587_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node5(v___x_2587_, v___x_2597_, v___x_2600_, v___x_2594_, v___x_2594_, v___x_2602_, v_a_2583_);
v___x_2604_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2596_, v___x_2603_);
v___x_2605_ = l_Lean_Syntax_node3(v___x_2587_, v___x_2588_, v___x_2590_, v___x_2595_, v___x_2604_);
v___x_2606_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2607_ = l_Lean_MessageData_ofName(v___y_2585_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = l_Lean_MessageData_ofExpr(v_e_2556_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v_fst_2566_ = v___x_2605_;
v_snd_2567_ = v___x_2612_;
v___y_2568_ = v___y_2560_;
v___y_2569_ = v___y_2561_;
v___y_2570_ = v___y_2562_;
v___y_2571_ = v___y_2563_;
goto v___jp_2565_;
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v___y_2562_);
lean_dec(v_h_x3f_2559_);
lean_dec(v_t_x3f_2557_);
lean_dec_ref(v_e_2556_);
v_a_2806_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2582_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2582_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
v___jp_2565_:
{
lean_object* v___x_2572_; lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2581_; 
v___x_2572_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_snd_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2570_);
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_fst_2566_);
lean_ctor_set(v___x_2577_, 1, v_a_2573_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object* v_e_2814_, lean_object* v_t_x3f_2815_, lean_object* v_a_2816_, lean_object* v_h_x3f_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_a_17931__boxed_2823_; lean_object* v_res_2824_; 
v_a_17931__boxed_2823_ = lean_unbox(v_a_2816_);
v_res_2824_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(v_e_2814_, v_t_x3f_2815_, v_a_17931__boxed_2823_, v_h_x3f_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2824_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1));
v___x_2829_ = l_Lean_MessageData_ofFormat(v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* v_ref_2830_, lean_object* v_h_x3f_2831_, lean_object* v_t_x3f_2832_, lean_object* v_e_2833_, lean_object* v_origSpan_x3f_2834_, lean_object* v_checkState_x3f_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_tac_2846_; lean_object* v_msg_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___x_2858_; 
lean_inc(v_a_2843_);
lean_inc_ref(v_a_2842_);
lean_inc(v_a_2841_);
lean_inc_ref(v_a_2840_);
lean_inc_ref(v_e_2833_);
v___x_2858_ = lean_infer_type(v_e_2833_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2858_);
v___x_2860_ = l_Lean_Meta_isProp(v_a_2859_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___f_2862_; lean_object* v___x_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___f_2862_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2862_, 0, v_e_2833_);
lean_closure_set(v___f_2862_, 1, v_t_x3f_2832_);
lean_closure_set(v___f_2862_, 2, v_a_2861_);
lean_closure_set(v___f_2862_, 3, v_h_x3f_2831_);
v___x_2863_ = l_Lean_Meta_withExposedNames___redArg(v___f_2862_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2863_);
if (lean_obj_tag(v_checkState_x3f_2835_) == 1)
{
lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v_val_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_fst_2865_ = lean_ctor_get(v_a_2864_, 0);
lean_inc(v_fst_2865_);
v_snd_2866_ = lean_ctor_get(v_a_2864_, 1);
lean_inc_n(v_snd_2866_, 2);
lean_dec(v_a_2864_);
v_val_2867_ = lean_ctor_get(v_checkState_x3f_2835_, 0);
lean_inc(v_val_2867_);
lean_dec_ref(v_checkState_x3f_2835_);
v___x_2868_ = lean_box(0);
v___x_2869_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_2865_, v_snd_2866_, v_val_2867_, v___x_2868_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
if (lean_obj_tag(v_a_2870_) == 1)
{
lean_object* v_val_2871_; lean_object* v_fst_2872_; lean_object* v_snd_2873_; 
lean_dec(v_snd_2866_);
v_val_2871_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_val_2871_);
lean_dec_ref(v_a_2870_);
v_fst_2872_ = lean_ctor_get(v_val_2871_, 0);
lean_inc(v_fst_2872_);
v_snd_2873_ = lean_ctor_get(v_val_2871_, 1);
lean_inc(v_snd_2873_);
lean_dec(v_val_2871_);
v_tac_2846_ = v_fst_2872_;
v_msg_2847_ = v_snd_2873_;
v___y_2848_ = v_a_2842_;
v___y_2849_ = v_a_2843_;
goto v___jp_2845_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec(v_a_2870_);
lean_dec(v_origSpan_x3f_2834_);
lean_dec(v_ref_2830_);
v___x_2874_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
v___x_2875_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_2874_, v_snd_2866_);
v___x_2876_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_2875_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2884_; 
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2876_, 0);
lean_dec(v_unused_2885_);
v___x_2878_ = v___x_2876_;
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
else
{
lean_dec(v___x_2876_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2884_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_box(0);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2880_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
else
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_snd_2866_);
lean_dec(v_origSpan_x3f_2834_);
lean_dec(v_ref_2830_);
v_a_2886_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2869_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2869_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_fst_2894_; lean_object* v_snd_2895_; 
lean_dec(v_checkState_x3f_2835_);
v_fst_2894_ = lean_ctor_get(v_a_2864_, 0);
lean_inc(v_fst_2894_);
v_snd_2895_ = lean_ctor_get(v_a_2864_, 1);
lean_inc(v_snd_2895_);
lean_dec(v_a_2864_);
v_tac_2846_ = v_fst_2894_;
v_msg_2847_ = v_snd_2895_;
v___y_2848_ = v_a_2842_;
v___y_2849_ = v_a_2843_;
goto v___jp_2845_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_checkState_x3f_2835_);
lean_dec(v_origSpan_x3f_2834_);
lean_dec(v_ref_2830_);
v_a_2896_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2863_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2863_);
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
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_checkState_x3f_2835_);
lean_dec(v_origSpan_x3f_2834_);
lean_dec_ref(v_e_2833_);
lean_dec(v_t_x3f_2832_);
lean_dec(v_h_x3f_2831_);
lean_dec(v_ref_2830_);
v_a_2904_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2860_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2860_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_checkState_x3f_2835_);
lean_dec(v_origSpan_x3f_2834_);
lean_dec_ref(v_e_2833_);
lean_dec(v_t_x3f_2832_);
lean_dec(v_h_x3f_2831_);
lean_dec(v_ref_2830_);
v_a_2912_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2858_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2858_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
v___jp_2845_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v_tac_2846_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_msg_2847_);
v___x_2854_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2851_);
lean_ctor_set(v___x_2854_, 1, v___x_2852_);
lean_ctor_set(v___x_2854_, 2, v___x_2852_);
lean_ctor_set(v___x_2854_, 3, v___x_2852_);
lean_ctor_set(v___x_2854_, 4, v___x_2853_);
lean_ctor_set(v___x_2854_, 5, v___x_2852_);
v___x_2855_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_2856_ = 4;
v___x_2857_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2830_, v___x_2854_, v_origSpan_x3f_2834_, v___x_2855_, v___x_2852_, v___x_2856_, v___y_2848_, v___y_2849_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object* v_ref_2920_, lean_object* v_h_x3f_2921_, lean_object* v_t_x3f_2922_, lean_object* v_e_2923_, lean_object* v_origSpan_x3f_2924_, lean_object* v_checkState_x3f_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(v_ref_2920_, v_h_x3f_2921_, v_t_x3f_2922_, v_e_2923_, v_origSpan_x3f_2924_, v_checkState_x3f_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
if (lean_obj_tag(v_a_2937_) == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = l_List_reverse___redArg(v_a_2938_);
return v___x_2939_;
}
else
{
lean_object* v_head_2940_; lean_object* v_tail_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2973_; 
v_head_2940_ = lean_ctor_get(v_a_2937_, 0);
v_tail_2941_ = lean_ctor_get(v_a_2937_, 1);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_a_2937_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2943_ = v_a_2937_;
v_isShared_2944_ = v_isSharedCheck_2973_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_tail_2941_);
lean_inc(v_head_2940_);
lean_dec(v_a_2937_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2973_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___y_2946_; lean_object* v_fst_2951_; lean_object* v_snd_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2972_; 
v_fst_2951_ = lean_ctor_get(v_head_2940_, 0);
v_snd_2952_ = lean_ctor_get(v_head_2940_, 1);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_head_2940_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2954_ = v_head_2940_;
v_isShared_2955_ = v_isSharedCheck_2972_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_snd_2952_);
lean_inc(v_fst_2951_);
lean_dec(v_head_2940_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2972_;
goto v_resetjp_2953_;
}
v___jp_2945_:
{
lean_object* v___x_2948_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v_a_2938_);
lean_ctor_set(v___x_2943_, 0, v___y_2946_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___y_2946_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_a_2938_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
v_a_2937_ = v_tail_2941_;
v_a_2938_ = v___x_2948_;
goto _start;
}
}
v_resetjp_2953_:
{
lean_object* v___y_2957_; uint8_t v___x_2969_; 
v___x_2969_ = lean_unbox(v_snd_2952_);
lean_dec(v_snd_2952_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; 
v___x_2970_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_2957_ = v___x_2970_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2971_; 
v___x_2971_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0));
v___y_2957_ = v___x_2971_;
goto v___jp_2956_;
}
v___jp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
lean_inc_ref(v___y_2957_);
v___x_2958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___y_2957_);
v___x_2959_ = l_Lean_MessageData_ofFormat(v___x_2958_);
v___x_2960_ = l_Lean_Expr_isConst(v_fst_2951_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = l_Lean_MessageData_ofExpr(v_fst_2951_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 7);
lean_ctor_set(v___x_2954_, 1, v___x_2961_);
lean_ctor_set(v___x_2954_, 0, v___x_2959_);
v___x_2963_ = v___x_2954_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
v___y_2946_ = v___x_2963_;
goto v___jp_2945_;
}
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = l_Lean_MessageData_ofConst(v_fst_2951_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 7);
lean_ctor_set(v___x_2954_, 1, v___x_2965_);
lean_ctor_set(v___x_2954_, 0, v___x_2959_);
v___x_2967_ = v___x_2954_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
v___y_2946_ = v___x_2967_;
goto v___jp_2945_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t v_sz_2981_, size_t v_i_2982_, lean_object* v_bs_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_usize_dec_lt(v_i_2982_, v_sz_2981_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_bs_2983_);
return v___x_2990_;
}
else
{
lean_object* v_v_2991_; lean_object* v_fst_2992_; lean_object* v_snd_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3037_; 
v_v_2991_ = lean_array_uget(v_bs_2983_, v_i_2982_);
v_fst_2992_ = lean_ctor_get(v_v_2991_, 0);
v_snd_2993_ = lean_ctor_get(v_v_2991_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_v_2991_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_2995_ = v_v_2991_;
v_isShared_2996_ = v_isSharedCheck_3037_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_snd_2993_);
lean_inc(v_fst_2992_);
lean_dec(v_v_2991_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3037_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v_bs_x27_2998_; lean_object* v_a_3000_; lean_object* v___x_3005_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v_bs_x27_2998_ = lean_array_uset(v_bs_2983_, v_i_2982_, v___x_2997_);
v___x_3005_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_fst_2992_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_3005_) == 0)
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_unbox(v_snd_2993_);
if (v___x_3006_ == 0)
{
lean_object* v_a_3007_; lean_object* v_ref_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_del_object(v___x_2995_);
v_a_3007_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3005_);
v_ref_3008_ = lean_ctor_get(v___y_2986_, 5);
v___x_3009_ = lean_unbox(v_snd_2993_);
lean_dec(v_snd_2993_);
v___x_3010_ = l_Lean_SourceInfo_fromRef(v_ref_3008_, v___x_3009_);
v___x_3011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3013_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
lean_inc(v___x_3010_);
v___x_3014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3010_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
lean_ctor_set(v___x_3014_, 2, v___x_3013_);
v___x_3015_ = l_Lean_Syntax_node2(v___x_3010_, v___x_3011_, v___x_3014_, v_a_3007_);
v_a_3000_ = v___x_3015_;
goto v___jp_2999_;
}
else
{
lean_object* v_a_3016_; lean_object* v_ref_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec(v_snd_2993_);
v_a_3016_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3016_);
lean_dec_ref(v___x_3005_);
v_ref_3017_ = lean_ctor_get(v___y_2986_, 5);
v___x_3018_ = 0;
v___x_3019_ = l_Lean_SourceInfo_fromRef(v_ref_3017_, v___x_3018_);
v___x_3020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2));
lean_inc(v___x_3019_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set_tag(v___x_2995_, 2);
lean_ctor_set(v___x_2995_, 1, v___x_3022_);
lean_ctor_set(v___x_2995_, 0, v___x_3019_);
v___x_3024_ = v___x_2995_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_inc(v___x_3019_);
v___x_3025_ = l_Lean_Syntax_node1(v___x_3019_, v___x_3021_, v___x_3024_);
v___x_3026_ = l_Lean_Syntax_node2(v___x_3019_, v___x_3020_, v___x_3025_, v_a_3016_);
v_a_3000_ = v___x_3026_;
goto v___jp_2999_;
}
}
}
else
{
lean_del_object(v___x_2995_);
lean_dec(v_snd_2993_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3028_; 
v_a_3028_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3028_);
lean_dec_ref(v___x_3005_);
v_a_3000_ = v_a_3028_;
goto v___jp_2999_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v_bs_x27_2998_);
v_a_3029_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3005_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3005_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
v___jp_2999_:
{
size_t v___x_3001_; size_t v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = ((size_t)1ULL);
v___x_3002_ = lean_usize_add(v_i_2982_, v___x_3001_);
v___x_3003_ = lean_array_uset(v_bs_x27_2998_, v_i_2982_, v_a_3000_);
v_i_2982_ = v___x_3002_;
v_bs_2983_ = v___x_3003_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object* v_sz_3038_, lean_object* v_i_3039_, lean_object* v_bs_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
size_t v_sz_boxed_3046_; size_t v_i_boxed_3047_; lean_object* v_res_3048_; 
v_sz_boxed_3046_ = lean_unbox_usize(v_sz_3038_);
lean_dec(v_sz_3038_);
v_i_boxed_3047_ = lean_unbox_usize(v_i_3039_);
lean_dec(v_i_3039_);
v_res_3048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_boxed_3046_, v_i_boxed_3047_, v_bs_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
return v_res_3048_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2));
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6));
v___x_3061_ = l_Lean_MessageData_ofFormat(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8));
v___x_3064_ = l_Lean_stringToMessageData(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object* v___x_3105_, lean_object* v_type_x3f_3106_, lean_object* v_rules_3107_, lean_object* v_loc_x3f_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v_extraMsg_3117_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; size_t v_sz_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v_sz_3162_ = lean_array_size(v___x_3105_);
v___x_3163_ = ((size_t)0ULL);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_3162_, v___x_3163_, v___x_3105_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v_a_3169_; lean_object* v_a_3194_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12));
v___x_3167_ = l_Lean_Syntax_SepArray_ofElems(v___x_3166_, v_a_3165_);
lean_dec(v_a_3165_);
if (lean_obj_tag(v_loc_x3f_3108_) == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_box(0);
v_a_3169_ = v___x_3196_;
goto v___jp_3168_;
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_val_3197_ = lean_ctor_get(v_loc_x3f_3108_, 0);
v___x_3198_ = lean_box(1);
lean_inc(v_val_3197_);
v___x_3199_ = l_Lean_PrettyPrinter_delab(v_val_3197_, v___x_3198_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v_ref_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref(v___x_3199_);
v_ref_3201_ = lean_ctor_get(v___y_3111_, 5);
v___x_3202_ = 0;
v___x_3203_ = l_Lean_SourceInfo_fromRef(v_ref_3201_, v___x_3202_);
v___x_3204_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24));
v___x_3205_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25));
lean_inc_n(v___x_3203_, 3);
v___x_3206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3203_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27));
v___x_3208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3209_ = l_Lean_Syntax_node1(v___x_3203_, v___x_3208_, v_a_3200_);
v___x_3210_ = l_Lean_Syntax_node1(v___x_3203_, v___x_3207_, v___x_3209_);
v___x_3211_ = l_Lean_Syntax_node2(v___x_3203_, v___x_3204_, v___x_3206_, v___x_3210_);
v_a_3194_ = v___x_3211_;
goto v___jp_3193_;
}
else
{
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3212_; 
v_a_3212_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___x_3199_);
v_a_3194_ = v_a_3212_;
goto v___jp_3193_;
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v_loc_x3f_3108_);
lean_dec_ref(v___x_3167_);
lean_dec(v_rules_3107_);
lean_dec(v_type_x3f_3106_);
v_a_3213_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3199_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3199_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
v___jp_3168_:
{
lean_object* v_ref_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_ref_3170_ = lean_ctor_get(v___y_3111_, 5);
v___x_3171_ = 0;
v___x_3172_ = l_Lean_SourceInfo_fromRef(v_ref_3170_, v___x_3171_);
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14));
v___x_3174_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15));
lean_inc_n(v___x_3172_, 7);
v___x_3175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3172_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17));
v___x_3177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3178_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_3179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3172_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
lean_ctor_set(v___x_3179_, 2, v___x_3178_);
v___x_3180_ = l_Lean_Syntax_node1(v___x_3172_, v___x_3176_, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19));
v___x_3182_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20));
v___x_3183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3172_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l_Array_append___redArg(v___x_3178_, v___x_3167_);
lean_dec_ref(v___x_3167_);
v___x_3185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3172_);
lean_ctor_set(v___x_3185_, 1, v___x_3177_);
lean_ctor_set(v___x_3185_, 2, v___x_3184_);
v___x_3186_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21));
v___x_3187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3172_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = l_Lean_Syntax_node3(v___x_3172_, v___x_3181_, v___x_3183_, v___x_3185_, v___x_3187_);
if (lean_obj_tag(v_a_3169_) == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___y_3137_ = v___x_3172_;
v___y_3138_ = v___x_3177_;
v___y_3139_ = v___x_3188_;
v___y_3140_ = v___x_3180_;
v___y_3141_ = v___x_3173_;
v___y_3142_ = v___x_3178_;
v___y_3143_ = v___x_3175_;
v___y_3144_ = v___x_3189_;
goto v___jp_3136_;
}
else
{
lean_object* v_val_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_val_3190_ = lean_ctor_get(v_a_3169_, 0);
lean_inc(v_val_3190_);
lean_dec_ref(v_a_3169_);
v___x_3191_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___x_3192_ = lean_array_push(v___x_3191_, v_val_3190_);
v___y_3137_ = v___x_3172_;
v___y_3138_ = v___x_3177_;
v___y_3139_ = v___x_3188_;
v___y_3140_ = v___x_3180_;
v___y_3141_ = v___x_3173_;
v___y_3142_ = v___x_3178_;
v___y_3143_ = v___x_3175_;
v___y_3144_ = v___x_3192_;
goto v___jp_3136_;
}
}
v___jp_3193_:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_a_3194_);
v_a_3169_ = v___x_3195_;
goto v___jp_3168_;
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_loc_x3f_3108_);
lean_dec(v_rules_3107_);
lean_dec(v_type_x3f_3106_);
v_a_3221_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3164_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3164_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
v___jp_3114_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___y_3116_);
lean_ctor_set(v___x_3118_, 1, v_extraMsg_3117_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___y_3115_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
v___jp_3121_:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___y_3123_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
switch(lean_obj_tag(v_type_x3f_3106_))
{
case 0:
{
lean_object* v_a_3125_; lean_object* v___x_3126_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref(v___x_3124_);
v___x_3126_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1);
v___y_3115_ = v___y_3122_;
v___y_3116_ = v_a_3125_;
v_extraMsg_3117_ = v___x_3126_;
goto v___jp_3114_;
}
case 1:
{
lean_object* v_a_3127_; lean_object* v_a_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_a_3133_; 
v_a_3127_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3124_);
v_a_3128_ = lean_ctor_get(v_type_x3f_3106_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v_type_x3f_3106_);
v___x_3129_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3);
v___x_3130_ = l_Lean_MessageData_ofExpr(v_a_3128_);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_3131_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3132_);
v___y_3115_ = v___y_3122_;
v___y_3116_ = v_a_3127_;
v_extraMsg_3117_ = v_a_3133_;
goto v___jp_3114_;
}
default: 
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3134_);
lean_dec_ref(v___x_3124_);
v___x_3135_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4);
v___y_3115_ = v___y_3122_;
v___y_3116_ = v_a_3134_;
v_extraMsg_3117_ = v___x_3135_;
goto v___jp_3114_;
}
}
}
v___jp_3136_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3145_ = l_Array_append___redArg(v___y_3142_, v___y_3144_);
lean_dec_ref(v___y_3144_);
lean_inc(v___y_3138_);
lean_inc(v___y_3137_);
v___x_3146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3146_, 0, v___y_3137_);
lean_ctor_set(v___x_3146_, 1, v___y_3138_);
lean_ctor_set(v___x_3146_, 2, v___x_3145_);
lean_inc(v___y_3141_);
v___x_3147_ = l_Lean_Syntax_node4(v___y_3137_, v___y_3141_, v___y_3143_, v___y_3140_, v___y_3139_, v___x_3146_);
v___x_3148_ = lean_box(0);
v___x_3149_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(v_rules_3107_, v___x_3148_);
v___x_3150_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7);
v___x_3151_ = l_Lean_MessageData_joinSep(v___x_3149_, v___x_3150_);
v___x_3152_ = l_Lean_MessageData_sbracket(v___x_3151_);
if (lean_obj_tag(v_loc_x3f_3108_) == 1)
{
lean_object* v_val_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_val_3153_ = lean_ctor_get(v_loc_x3f_3108_, 0);
lean_inc(v_val_3153_);
lean_dec_ref(v_loc_x3f_3108_);
v___x_3154_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v___x_3152_);
v___x_3156_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11);
v___x_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Lean_MessageData_ofExpr(v_val_3153_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___y_3122_ = v___x_3147_;
v___y_3123_ = v___x_3159_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec(v_loc_x3f_3108_);
v___x_3160_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3152_);
v___y_3122_ = v___x_3147_;
v___y_3123_ = v___x_3161_;
goto v___jp_3121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(lean_object* v___x_3229_, lean_object* v_type_x3f_3230_, lean_object* v_rules_3231_, lean_object* v_loc_x3f_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(v___x_3229_, v_type_x3f_3230_, v_rules_3231_, v_loc_x3f_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3238_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1));
v___x_3243_ = l_Lean_MessageData_ofFormat(v___x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* v_ref_3244_, lean_object* v_rules_3245_, lean_object* v_type_x3f_3246_, lean_object* v_loc_x3f_3247_, lean_object* v_origSpan_x3f_3248_, lean_object* v_checkState_x3f_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; 
lean_inc(v_rules_3245_);
v___x_3259_ = lean_array_mk(v_rules_3245_);
lean_inc(v_type_x3f_3246_);
v___f_3260_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3260_, 0, v___x_3259_);
lean_closure_set(v___f_3260_, 1, v_type_x3f_3246_);
lean_closure_set(v___f_3260_, 2, v_rules_3245_);
lean_closure_set(v___f_3260_, 3, v_loc_x3f_3247_);
v___x_3261_ = l_Lean_Meta_withExposedNames___redArg(v___f_3260_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v_snd_3263_; lean_object* v_fst_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3334_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref(v___x_3261_);
v_snd_3263_ = lean_ctor_get(v_a_3262_, 1);
v_fst_3264_ = lean_ctor_get(v_a_3262_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_a_3262_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3266_ = v_a_3262_;
v_isShared_3267_ = v_isSharedCheck_3334_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_snd_3263_);
lean_inc(v_fst_3264_);
lean_dec(v_a_3262_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3334_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3333_; 
v_fst_3268_ = lean_ctor_get(v_snd_3263_, 0);
v_snd_3269_ = lean_ctor_get(v_snd_3263_, 1);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_snd_3263_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3271_ = v_snd_3263_;
v_isShared_3272_ = v_isSharedCheck_3333_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_snd_3269_);
lean_inc(v_fst_3268_);
lean_dec(v_snd_3263_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3333_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_tac_3274_; lean_object* v_tacMsg_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; 
if (lean_obj_tag(v_checkState_x3f_3249_) == 1)
{
lean_object* v_val_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3332_; 
v_val_3291_ = lean_ctor_get(v_checkState_x3f_3249_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_checkState_x3f_3249_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3293_ = v_checkState_x3f_3249_;
v_isShared_3294_ = v_isSharedCheck_3332_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_val_3291_);
lean_dec(v_checkState_x3f_3249_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3332_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___y_3296_; 
if (lean_obj_tag(v_type_x3f_3246_) == 1)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; 
v_a_3327_ = lean_ctor_get(v_type_x3f_3246_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v_type_x3f_3246_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v_a_3327_);
v___x_3329_ = v___x_3293_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
v___y_3296_ = v___x_3329_;
goto v___jp_3295_;
}
}
else
{
lean_object* v___x_3331_; 
lean_del_object(v___x_3293_);
lean_dec(v_type_x3f_3246_);
v___x_3331_ = lean_box(0);
v___y_3296_ = v___x_3331_;
goto v___jp_3295_;
}
v___jp_3295_:
{
lean_object* v___x_3297_; 
lean_inc(v_fst_3268_);
v___x_3297_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_3264_, v_fst_3268_, v_val_3291_, v___y_3296_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3297_);
if (lean_obj_tag(v_a_3298_) == 1)
{
lean_object* v_val_3299_; lean_object* v_fst_3300_; lean_object* v_snd_3301_; 
lean_dec(v_fst_3268_);
v_val_3299_ = lean_ctor_get(v_a_3298_, 0);
lean_inc(v_val_3299_);
lean_dec_ref(v_a_3298_);
v_fst_3300_ = lean_ctor_get(v_val_3299_, 0);
lean_inc(v_fst_3300_);
v_snd_3301_ = lean_ctor_get(v_val_3299_, 1);
lean_inc(v_snd_3301_);
lean_dec(v_val_3299_);
v_tac_3274_ = v_fst_3300_;
v_tacMsg_3275_ = v_snd_3301_;
v___y_3276_ = v_a_3256_;
v___y_3277_ = v_a_3257_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_a_3298_);
lean_del_object(v___x_3271_);
lean_del_object(v___x_3266_);
lean_dec(v_origSpan_x3f_3248_);
lean_dec(v_ref_3244_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v_fst_3268_);
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v_snd_3269_);
v___x_3308_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_3306_, v___x_3307_);
v___x_3309_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_3308_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3317_; 
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3309_, 0);
lean_dec(v_unused_3318_);
v___x_3311_ = v___x_3309_;
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
else
{
lean_dec(v___x_3309_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = lean_box(0);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3313_);
v___x_3315_ = v___x_3311_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
return v___x_3309_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_del_object(v___x_3271_);
lean_dec(v_snd_3269_);
lean_dec(v_fst_3268_);
lean_del_object(v___x_3266_);
lean_dec(v_origSpan_x3f_3248_);
lean_dec(v_ref_3244_);
v_a_3319_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3297_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3297_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
}
else
{
lean_dec(v_checkState_x3f_3249_);
lean_dec(v_type_x3f_3246_);
v_tac_3274_ = v_fst_3264_;
v_tacMsg_3275_ = v_fst_3268_;
v___y_3276_ = v_a_3256_;
v___y_3277_ = v_a_3257_;
goto v___jp_3273_;
}
v___jp_3273_:
{
lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 1, v_tac_3274_);
lean_ctor_set(v___x_3271_, 0, v___x_3278_);
v___x_3280_ = v___x_3271_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_tac_3274_);
v___x_3280_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = lean_box(0);
if (v_isShared_3267_ == 0)
{
lean_ctor_set_tag(v___x_3266_, 7);
lean_ctor_set(v___x_3266_, 1, v_snd_3269_);
lean_ctor_set(v___x_3266_, 0, v_tacMsg_3275_);
v___x_3283_ = v___x_3266_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_tacMsg_3275_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_snd_3269_);
v___x_3283_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3280_);
lean_ctor_set(v___x_3285_, 1, v___x_3281_);
lean_ctor_set(v___x_3285_, 2, v___x_3281_);
lean_ctor_set(v___x_3285_, 3, v___x_3281_);
lean_ctor_set(v___x_3285_, 4, v___x_3284_);
lean_ctor_set(v___x_3285_, 5, v___x_3281_);
v___x_3286_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_3287_ = 4;
v___x_3288_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3244_, v___x_3285_, v_origSpan_x3f_3248_, v___x_3286_, v___x_3281_, v___x_3287_, v___y_3276_, v___y_3277_);
return v___x_3288_;
}
}
}
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_checkState_x3f_3249_);
lean_dec(v_origSpan_x3f_3248_);
lean_dec(v_type_x3f_3246_);
lean_dec(v_ref_3244_);
v_a_3335_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3261_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3261_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object* v_ref_3343_, lean_object* v_rules_3344_, lean_object* v_type_x3f_3345_, lean_object* v_loc_x3f_3346_, lean_object* v_origSpan_x3f_3347_, lean_object* v_checkState_x3f_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3343_, v_rules_3344_, v_type_x3f_3345_, v_loc_x3f_3346_, v_origSpan_x3f_3347_, v_checkState_x3f_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v_res_3358_;
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
