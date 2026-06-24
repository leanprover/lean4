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
lean_dec_ref_known(v___x_277_, 14);
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
lean_dec_ref_known(v___x_340_, 1);
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
uint8_t v___y_2411__boxed_445_; uint8_t v_suppressElabErrors_boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v___y_2411__boxed_445_ = lean_unbox(v___y_442_);
v_suppressElabErrors_boxed_446_ = lean_unbox(v_suppressElabErrors_443_);
v_res_447_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0(v___y_2411__boxed_445_, v_suppressElabErrors_boxed_446_, v_x_444_);
lean_dec(v_x_444_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0(lean_object* v_ref_450_, lean_object* v_msgData_451_, uint8_t v_severity_452_, uint8_t v_isSilent_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_496_; uint8_t v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v___y_519_; uint8_t v___y_520_; lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; uint8_t v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; uint8_t v___y_536_; uint8_t v___x_541_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___y_551_; uint8_t v___x_566_; 
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
lean_ctor_set(v___x_483_, 1, v___y_463_);
lean_inc_ref(v___y_460_);
lean_inc_ref(v___y_458_);
v___x_484_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_484_, 0, v___y_458_);
lean_ctor_set(v___x_484_, 1, v___y_461_);
lean_ctor_set(v___x_484_, 2, v___y_462_);
lean_ctor_set(v___x_484_, 3, v___y_460_);
lean_ctor_set(v___x_484_, 4, v___x_483_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5, v___y_459_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5 + 1, v___y_464_);
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
lean_inc_ref_n(v___y_498_, 2);
v___x_508_ = l_Lean_FileMap_toPosition(v___y_498_, v___y_499_);
lean_dec(v___y_499_);
v___x_509_ = l_Lean_FileMap_toPosition(v___y_498_, v___y_501_);
lean_dec(v___y_501_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_495_ == 0)
{
lean_del_object(v___x_506_);
lean_dec_ref(v___y_494_);
v___y_458_ = v___y_496_;
v___y_459_ = v___y_497_;
v___y_460_ = v___x_511_;
v___y_461_ = v___x_508_;
v___y_462_ = v___x_510_;
v___y_463_ = v_a_504_;
v___y_464_ = v___y_500_;
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
lean_dec_ref_known(v___x_510_, 1);
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
v___y_458_ = v___y_496_;
v___y_459_ = v___y_497_;
v___y_460_ = v___x_511_;
v___y_461_ = v___x_508_;
v___y_462_ = v___x_510_;
v___y_463_ = v_a_504_;
v___y_464_ = v___y_500_;
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
v___x_527_ = l_Lean_Syntax_getTailPos_x3f(v___y_524_, v___y_522_);
lean_dec(v___y_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_inc(v___y_526_);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_520_;
v___y_496_ = v___y_521_;
v___y_497_ = v___y_522_;
v___y_498_ = v___y_523_;
v___y_499_ = v___y_526_;
v___y_500_ = v___y_525_;
v___y_501_ = v___y_526_;
goto v___jp_493_;
}
else
{
lean_object* v_val_528_; 
v_val_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v___x_527_, 1);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_520_;
v___y_496_ = v___y_521_;
v___y_497_ = v___y_522_;
v___y_498_ = v___y_523_;
v___y_499_ = v___y_526_;
v___y_500_ = v___y_525_;
v___y_501_ = v_val_528_;
goto v___jp_493_;
}
}
v___jp_529_:
{
lean_object* v_ref_537_; lean_object* v___x_538_; 
v_ref_537_ = l_Lean_replaceRef(v_ref_450_, v___y_535_);
v___x_538_ = l_Lean_Syntax_getPos_x3f(v_ref_537_, v___y_533_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___y_519_ = v___y_530_;
v___y_520_ = v___y_531_;
v___y_521_ = v___y_532_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_534_;
v___y_524_ = v_ref_537_;
v___y_525_ = v___y_536_;
v___y_526_ = v___x_539_;
goto v___jp_518_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v___x_538_, 1);
v___y_519_ = v___y_530_;
v___y_520_ = v___y_531_;
v___y_521_ = v___y_532_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_534_;
v___y_524_ = v_ref_537_;
v___y_525_ = v___y_536_;
v___y_526_ = v_val_540_;
goto v___jp_518_;
}
}
v___jp_542_:
{
if (v___y_549_ == 0)
{
v___y_530_ = v___y_543_;
v___y_531_ = v___y_544_;
v___y_532_ = v___y_545_;
v___y_533_ = v___y_548_;
v___y_534_ = v___y_546_;
v___y_535_ = v___y_547_;
v___y_536_ = v_severity_452_;
goto v___jp_529_;
}
else
{
v___y_530_ = v___y_543_;
v___y_531_ = v___y_544_;
v___y_532_ = v___y_545_;
v___y_533_ = v___y_548_;
v___y_534_ = v___y_546_;
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
v___y_543_ = v___f_559_;
v___y_544_ = v_suppressElabErrors_556_;
v___y_545_ = v_fileName_552_;
v___y_546_ = v_fileMap_553_;
v___y_547_ = v_ref_555_;
v___y_548_ = v___y_551_;
v___y_549_ = v___x_561_;
goto v___jp_542_;
}
else
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = l_Lean_warningAsError;
v___x_563_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_554_, v___x_562_);
v___y_543_ = v___f_559_;
v___y_544_ = v_suppressElabErrors_556_;
v___y_545_ = v_fileName_552_;
v___y_546_ = v_fileMap_553_;
v___y_547_ = v_ref_555_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* v_ref_592_, lean_object* v_s_593_, lean_object* v_origSpan_x3f_594_, lean_object* v_header_595_, lean_object* v_codeActionPrefix_x3f_596_, uint8_t v_diffGranularity_597_, lean_object* v_footer_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_602_; lean_object* v_hintSuggestion_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; 
v___x_602_ = lean_box(0);
v_hintSuggestion_603_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_hintSuggestion_603_, 0, v_s_593_);
lean_ctor_set(v_hintSuggestion_603_, 1, v_origSpan_x3f_594_);
lean_ctor_set(v_hintSuggestion_603_, 2, v___x_602_);
lean_ctor_set_uint8(v_hintSuggestion_603_, sizeof(void*)*3, v_diffGranularity_597_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_array_push(v___x_605_, v_hintSuggestion_603_);
v___x_607_ = 0;
lean_inc(v_ref_592_);
v___x_608_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v___x_606_, v_ref_592_, v_codeActionPrefix_x3f_596_, v___x_607_, v_a_599_, v_a_600_);
lean_dec_ref(v___x_606_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = l_Lean_stringToMessageData(v_header_595_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_a_609_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_footer_598_);
v___x_613_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_592_, v___x_612_, v_a_599_, v_a_600_);
lean_dec(v_ref_592_);
return v___x_613_;
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_footer_598_);
lean_dec_ref(v_header_595_);
lean_dec(v_ref_592_);
v_a_614_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_608_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_608_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* v_ref_622_, lean_object* v_s_623_, lean_object* v_origSpan_x3f_624_, lean_object* v_header_625_, lean_object* v_codeActionPrefix_x3f_626_, lean_object* v_diffGranularity_627_, lean_object* v_footer_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
uint8_t v_diffGranularity_boxed_632_; lean_object* v_res_633_; 
v_diffGranularity_boxed_632_ = lean_unbox(v_diffGranularity_627_);
v_res_633_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_622_, v_s_623_, v_origSpan_x3f_624_, v_header_625_, v_codeActionPrefix_x3f_626_, v_diffGranularity_boxed_632_, v_footer_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_ref_638_; lean_object* v___x_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_ref_638_ = lean_ctor_get(v___y_635_, 5);
v___x_639_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0_spec__1(v_msg_634_, v___y_635_, v___y_636_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
lean_inc(v_ref_638_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_ref_638_);
lean_ctor_set(v___x_644_, 1, v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg___boxed(lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(lean_object* v_ref_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_fileName_659_; lean_object* v_fileMap_660_; lean_object* v_options_661_; lean_object* v_currRecDepth_662_; lean_object* v_maxRecDepth_663_; lean_object* v_ref_664_; lean_object* v_currNamespace_665_; lean_object* v_openDecls_666_; lean_object* v_initHeartbeats_667_; lean_object* v_maxHeartbeats_668_; lean_object* v_quotContext_669_; lean_object* v_currMacroScope_670_; uint8_t v_diag_671_; lean_object* v_cancelTk_x3f_672_; uint8_t v_suppressElabErrors_673_; lean_object* v_inheritedTraceOptions_674_; lean_object* v_ref_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_fileName_659_ = lean_ctor_get(v___y_656_, 0);
v_fileMap_660_ = lean_ctor_get(v___y_656_, 1);
v_options_661_ = lean_ctor_get(v___y_656_, 2);
v_currRecDepth_662_ = lean_ctor_get(v___y_656_, 3);
v_maxRecDepth_663_ = lean_ctor_get(v___y_656_, 4);
v_ref_664_ = lean_ctor_get(v___y_656_, 5);
v_currNamespace_665_ = lean_ctor_get(v___y_656_, 6);
v_openDecls_666_ = lean_ctor_get(v___y_656_, 7);
v_initHeartbeats_667_ = lean_ctor_get(v___y_656_, 8);
v_maxHeartbeats_668_ = lean_ctor_get(v___y_656_, 9);
v_quotContext_669_ = lean_ctor_get(v___y_656_, 10);
v_currMacroScope_670_ = lean_ctor_get(v___y_656_, 11);
v_diag_671_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*14);
v_cancelTk_x3f_672_ = lean_ctor_get(v___y_656_, 12);
v_suppressElabErrors_673_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_674_ = lean_ctor_get(v___y_656_, 13);
v_ref_675_ = l_Lean_replaceRef(v_ref_654_, v_ref_664_);
lean_inc_ref(v_inheritedTraceOptions_674_);
lean_inc(v_cancelTk_x3f_672_);
lean_inc(v_currMacroScope_670_);
lean_inc(v_quotContext_669_);
lean_inc(v_maxHeartbeats_668_);
lean_inc(v_initHeartbeats_667_);
lean_inc(v_openDecls_666_);
lean_inc(v_currNamespace_665_);
lean_inc(v_maxRecDepth_663_);
lean_inc(v_currRecDepth_662_);
lean_inc_ref(v_options_661_);
lean_inc_ref(v_fileMap_660_);
lean_inc_ref(v_fileName_659_);
v___x_676_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_676_, 0, v_fileName_659_);
lean_ctor_set(v___x_676_, 1, v_fileMap_660_);
lean_ctor_set(v___x_676_, 2, v_options_661_);
lean_ctor_set(v___x_676_, 3, v_currRecDepth_662_);
lean_ctor_set(v___x_676_, 4, v_maxRecDepth_663_);
lean_ctor_set(v___x_676_, 5, v_ref_675_);
lean_ctor_set(v___x_676_, 6, v_currNamespace_665_);
lean_ctor_set(v___x_676_, 7, v_openDecls_666_);
lean_ctor_set(v___x_676_, 8, v_initHeartbeats_667_);
lean_ctor_set(v___x_676_, 9, v_maxHeartbeats_668_);
lean_ctor_set(v___x_676_, 10, v_quotContext_669_);
lean_ctor_set(v___x_676_, 11, v_currMacroScope_670_);
lean_ctor_set(v___x_676_, 12, v_cancelTk_x3f_672_);
lean_ctor_set(v___x_676_, 13, v_inheritedTraceOptions_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*14, v_diag_671_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*14 + 1, v_suppressElabErrors_673_);
v___x_677_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_655_, v___x_676_, v___y_657_);
lean_dec_ref_known(v___x_676_, 14);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg___boxed(lean_object* v_ref_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_678_, v_msg_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v_ref_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(lean_object* v_origSpan_x3f_684_, uint8_t v_diffGranularity_685_, size_t v_sz_686_, size_t v_i_687_, lean_object* v_bs_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_lt(v_i_687_, v_sz_686_);
if (v___x_689_ == 0)
{
lean_dec(v_origSpan_x3f_684_);
return v_bs_688_;
}
else
{
lean_object* v_v_690_; lean_object* v___x_691_; lean_object* v_bs_x27_692_; lean_object* v___x_693_; lean_object* v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v_v_690_ = lean_array_uget(v_bs_688_, v_i_687_);
v___x_691_ = lean_unsigned_to_nat(0u);
v_bs_x27_692_ = lean_array_uset(v_bs_688_, v_i_687_, v___x_691_);
v___x_693_ = lean_box(0);
lean_inc(v_origSpan_x3f_684_);
v___x_694_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_694_, 0, v_v_690_);
lean_ctor_set(v___x_694_, 1, v_origSpan_x3f_684_);
lean_ctor_set(v___x_694_, 2, v___x_693_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*3, v_diffGranularity_685_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_687_, v___x_695_);
v___x_697_ = lean_array_uset(v_bs_x27_692_, v_i_687_, v___x_694_);
v_i_687_ = v___x_696_;
v_bs_688_ = v___x_697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object* v_origSpan_x3f_699_, lean_object* v_diffGranularity_700_, lean_object* v_sz_701_, lean_object* v_i_702_, lean_object* v_bs_703_){
_start:
{
uint8_t v_diffGranularity_boxed_704_; size_t v_sz_boxed_705_; size_t v_i_boxed_706_; lean_object* v_res_707_; 
v_diffGranularity_boxed_704_ = lean_unbox(v_diffGranularity_700_);
v_sz_boxed_705_ = lean_unbox_usize(v_sz_701_);
lean_dec(v_sz_701_);
v_i_boxed_706_ = lean_unbox_usize(v_i_702_);
lean_dec(v_i_702_);
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_699_, v_diffGranularity_boxed_704_, v_sz_boxed_705_, v_i_boxed_706_, v_bs_703_);
return v_res_707_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__0));
v___x_710_ = l_Lean_stringToMessageData(v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object* v_ref_711_, lean_object* v_suggestions_712_, lean_object* v_origSpan_x3f_713_, lean_object* v_header_714_, lean_object* v_codeActionPrefix_x3f_715_, uint8_t v_diffGranularity_716_, lean_object* v_footer_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_array_get_size(v_suggestions_712_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
v___y_722_ = v_a_718_;
v___y_723_ = v_a_719_;
goto v___jp_721_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v_footer_717_);
lean_dec(v_codeActionPrefix_x3f_715_);
lean_dec_ref(v_header_714_);
lean_dec(v_origSpan_x3f_713_);
lean_dec_ref(v_suggestions_712_);
v___x_745_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1, &l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___closed__1);
v___x_746_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_711_, v___x_745_, v_a_718_, v_a_719_);
lean_dec(v_ref_711_);
return v___x_746_;
}
v___jp_721_:
{
size_t v_sz_724_; size_t v___x_725_; lean_object* v_hintSuggestions_726_; uint8_t v___x_727_; lean_object* v___x_728_; 
v_sz_724_ = lean_array_size(v_suggestions_712_);
v___x_725_ = ((size_t)0ULL);
v_hintSuggestions_726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(v_origSpan_x3f_713_, v_diffGranularity_716_, v_sz_724_, v___x_725_, v_suggestions_712_);
v___x_727_ = 1;
lean_inc(v_ref_711_);
v___x_728_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_hintSuggestions_726_, v_ref_711_, v_codeActionPrefix_x3f_715_, v___x_727_, v___y_722_, v___y_723_);
lean_dec_ref(v_hintSuggestions_726_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = l_Lean_stringToMessageData(v_header_714_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_a_729_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_footer_717_);
v___x_733_ = l_Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(v_ref_711_, v___x_732_, v___y_722_, v___y_723_);
lean_dec(v_ref_711_);
return v___x_733_;
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v_footer_717_);
lean_dec_ref(v_header_714_);
lean_dec(v_ref_711_);
v_a_734_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_728_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_728_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg___boxed(lean_object* v_ref_747_, lean_object* v_suggestions_748_, lean_object* v_origSpan_x3f_749_, lean_object* v_header_750_, lean_object* v_codeActionPrefix_x3f_751_, lean_object* v_diffGranularity_752_, lean_object* v_footer_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_diffGranularity_boxed_757_; lean_object* v_res_758_; 
v_diffGranularity_boxed_757_ = lean_unbox(v_diffGranularity_752_);
v_res_758_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_747_, v_suggestions_748_, v_origSpan_x3f_749_, v_header_750_, v_codeActionPrefix_x3f_751_, v_diffGranularity_boxed_757_, v_footer_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object* v_ref_759_, lean_object* v_suggestions_760_, lean_object* v_origSpan_x3f_761_, lean_object* v_header_762_, lean_object* v_style_x3f_763_, lean_object* v_codeActionPrefix_x3f_764_, uint8_t v_diffGranularity_765_, lean_object* v_footer_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_759_, v_suggestions_760_, v_origSpan_x3f_761_, v_header_762_, v_codeActionPrefix_x3f_764_, v_diffGranularity_765_, v_footer_766_, v_a_767_, v_a_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object* v_ref_771_, lean_object* v_suggestions_772_, lean_object* v_origSpan_x3f_773_, lean_object* v_header_774_, lean_object* v_style_x3f_775_, lean_object* v_codeActionPrefix_x3f_776_, lean_object* v_diffGranularity_777_, lean_object* v_footer_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
uint8_t v_diffGranularity_boxed_782_; lean_object* v_res_783_; 
v_diffGranularity_boxed_782_ = lean_unbox(v_diffGranularity_777_);
v_res_783_ = l_Lean_Meta_Tactic_TryThis_addSuggestions(v_ref_771_, v_suggestions_772_, v_origSpan_x3f_773_, v_header_774_, v_style_x3f_775_, v_codeActionPrefix_x3f_776_, v_diffGranularity_boxed_782_, v_footer_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_style_x3f_775_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object* v_00_u03b1_784_, lean_object* v_ref_785_, lean_object* v_msg_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___redArg(v_ref_785_, v_msg_786_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object* v_00_u03b1_791_, lean_object* v_ref_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(v_00_u03b1_791_, v_ref_792_, v_msg_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_ref_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(lean_object* v_00_u03b1_798_, lean_object* v_msg_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___redArg(v_msg_799_, v___y_800_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1___boxed(lean_object* v_00_u03b1_804_, lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Tactic_TryThis_addSuggestions_spec__1_spec__1(v_00_u03b1_804_, v_msg_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(lean_object* v_a_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
v___x_820_ = lean_apply_2(v_a_810_, v___y_811_, v___y_812_);
v___x_821_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_820_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg___boxed(lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(lean_object* v_00_u03b1_833_, lean_object* v_a_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v_a_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___boxed(lean_object* v_00_u03b1_845_, lean_object* v_a_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0(v_00_u03b1_845_, v_a_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(lean_object* v_e_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = l_Lean_Expr_hasMVar(v_e_857_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_e_857_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v___x_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_867_; lean_object* v_cache_868_; lean_object* v_zetaDeltaFVarIds_869_; lean_object* v_postponed_870_; lean_object* v_diag_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
v___x_862_ = lean_st_ref_get(v___y_858_);
v_mctx_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc_ref(v_mctx_863_);
lean_dec(v___x_862_);
v___x_864_ = l_Lean_instantiateMVarsCore(v_mctx_863_, v_e_857_);
v_fst_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_fst_865_);
v_snd_866_ = lean_ctor_get(v___x_864_, 1);
lean_inc(v_snd_866_);
lean_dec_ref(v___x_864_);
v___x_867_ = lean_st_ref_take(v___y_858_);
v_cache_868_ = lean_ctor_get(v___x_867_, 1);
v_zetaDeltaFVarIds_869_ = lean_ctor_get(v___x_867_, 2);
v_postponed_870_ = lean_ctor_get(v___x_867_, 3);
v_diag_871_ = lean_ctor_get(v___x_867_, 4);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_881_);
v___x_873_ = v___x_867_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_diag_871_);
lean_inc(v_postponed_870_);
lean_inc(v_zetaDeltaFVarIds_869_);
lean_inc(v_cache_868_);
lean_dec(v___x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_snd_866_);
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_snd_866_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_cache_868_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_zetaDeltaFVarIds_869_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_postponed_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_diag_871_);
v___x_876_ = v_reuseFailAlloc_879_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_st_ref_set(v___y_858_, v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_fst_865_);
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg___boxed(lean_object* v_e_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_882_, v___y_883_);
lean_dec(v___y_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(lean_object* v_e_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_e_886_, v___y_892_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___boxed(lean_object* v_e_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1(v_e_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_ref_914_; lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_ref_914_ = lean_ctor_get(v___y_911_, 5);
v___x_915_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_msg_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_inc(v_ref_914_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_ref_914_);
lean_ctor_set(v___x_920_, 1, v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg___boxed(lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_msg_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* v_initialState_935_, lean_object* v_tac_936_, lean_object* v_expectedType_x3f_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_939_, v_a_941_, v_a_943_, v_a_945_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; uint8_t v___x_949_; lean_object* v_a_951_; lean_object* v_a_962_; lean_object* v___y_973_; lean_object* v___x_976_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = 0;
v___x_976_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_initialState_935_, v___x_949_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec_ref_known(v___x_976_, 1);
v___x_977_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_977_, 0, v_tac_936_);
v___x_978_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_978_, 0, lean_box(0));
lean_closure_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__0___redArg(v___x_978_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec_ref_known(v___x_979_, 1);
if (lean_obj_tag(v_expectedType_x3f_937_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_981_; 
v_val_980_ = lean_ctor_get(v_expectedType_x3f_937_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v_expectedType_x3f_937_, 1);
v___x_981_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_939_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_MVarId_getType(v_a_982_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v_a_988_; uint8_t v___x_989_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_984_, v_a_943_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_val_980_, v_a_943_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = lean_expr_eqv(v_a_986_, v_a_988_);
lean_dec(v_a_988_);
lean_dec(v_a_986_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
v___x_991_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v___x_990_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
v___y_973_ = v___x_991_;
goto v___jp_972_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_box(0);
v_a_962_ = v___x_992_;
goto v___jp_961_;
}
}
else
{
lean_object* v_a_993_; 
lean_dec(v_val_980_);
v_a_993_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_983_, 1);
v_a_951_ = v_a_993_;
goto v___jp_950_;
}
}
else
{
lean_object* v_a_994_; 
lean_dec(v_val_980_);
v_a_994_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_981_, 1);
v_a_951_ = v_a_994_;
goto v___jp_950_;
}
}
else
{
lean_object* v___x_995_; 
lean_dec(v_expectedType_x3f_937_);
v___x_995_ = lean_box(0);
v_a_962_ = v___x_995_;
goto v___jp_961_;
}
}
else
{
lean_dec(v_expectedType_x3f_937_);
v___y_973_ = v___x_979_;
goto v___jp_972_;
}
}
else
{
lean_dec(v_a_948_);
lean_dec(v_expectedType_x3f_937_);
lean_dec(v_tac_936_);
return v___x_976_;
}
v___jp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_948_, v___x_949_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_960_);
v___x_954_ = v___x_952_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_952_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 1);
lean_ctor_set(v___x_954_, 0, v_a_951_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_951_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
else
{
lean_dec_ref(v_a_951_);
return v___x_952_;
}
}
v___jp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_948_, v___x_949_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_971_);
v___x_965_ = v___x_963_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_dec(v___x_963_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_a_962_);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_962_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
return v___x_963_;
}
}
v___jp_972_:
{
if (lean_obj_tag(v___y_973_) == 0)
{
lean_object* v_a_974_; 
v_a_974_ = lean_ctor_get(v___y_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___y_973_, 1);
v_a_962_ = v_a_974_;
goto v___jp_961_;
}
else
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v___y_973_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___y_973_, 1);
v_a_951_ = v_a_975_;
goto v___jp_950_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_expectedType_x3f_937_);
lean_dec(v_tac_936_);
lean_dec_ref(v_initialState_935_);
v_a_996_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_947_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_947_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* v_tac_1078_, lean_object* v_msg_1079_, lean_object* v_initialState_1080_, lean_object* v_expectedType_x3f_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1083_, v_a_1085_, v_a_1087_, v_a_1089_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
lean_inc(v_expectedType_x3f_1081_);
lean_inc(v_tac_1078_);
lean_inc_ref(v_initialState_1080_);
v___x_1116_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1080_, v_tac_1078_, v_expectedType_x3f_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1115_);
lean_dec(v_expectedType_x3f_1081_);
lean_dec_ref(v_initialState_1080_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1116_, 0);
lean_dec(v_unused_1126_);
v___x_1118_ = v___x_1116_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_dec(v___x_1116_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_tac_1078_);
lean_ctor_set(v___x_1120_, 1, v_msg_1079_);
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1195_; 
v_a_1127_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1129_ = v___x_1116_;
v_isShared_1130_ = v_isSharedCheck_1195_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1116_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1195_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___y_1132_; uint8_t v___x_1193_; 
v___x_1193_ = l_Lean_Exception_isInterrupt(v_a_1127_);
if (v___x_1193_ == 0)
{
uint8_t v___x_1194_; 
lean_inc(v_a_1127_);
v___x_1194_ = l_Lean_Exception_isRuntime(v_a_1127_);
v___y_1132_ = v___x_1194_;
goto v___jp_1131_;
}
else
{
v___y_1132_ = v___x_1193_;
goto v___jp_1131_;
}
v___jp_1131_:
{
if (v___y_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_del_object(v___x_1129_);
lean_dec(v_a_1127_);
v___x_1133_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_1115_, v___y_1132_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_ref_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref_known(v___x_1133_, 1);
v_ref_1134_ = lean_ctor_get(v_a_1088_, 5);
v___x_1135_ = l_Lean_SourceInfo_fromRef(v_ref_1134_, v___y_1132_);
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2));
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3));
lean_inc_n(v___x_1135_, 6);
v___x_1138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1135_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5));
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7));
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11));
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12));
v___x_1144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1135_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1142_, v___x_1144_);
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13));
v___x_1147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1135_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_Syntax_node3(v___x_1135_, v___x_1141_, v___x_1145_, v___x_1147_, v_tac_1078_);
v___x_1149_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1140_, v___x_1148_);
v___x_1150_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_1083_, v_a_1085_, v_a_1087_, v_a_1089_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
lean_inc_n(v___x_1135_, 2);
v___x_1152_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1139_, v___x_1149_);
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14));
v___x_1154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1135_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node3(v___x_1135_, v___x_1136_, v___x_1138_, v___x_1152_, v___x_1154_);
lean_inc(v___x_1155_);
v___x_1156_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(v_initialState_1080_, v___x_1155_, v_expectedType_x3f_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_a_1151_);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v___x_1156_, 0);
lean_dec(v_unused_1170_);
v___x_1158_ = v___x_1156_;
v_isShared_1159_ = v_isSharedCheck_1169_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v___x_1156_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1169_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_msg_1079_);
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1155_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1165_);
v___x_1167_ = v___x_1158_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1171_; uint8_t v___x_1172_; 
lean_dec(v___x_1155_);
lean_dec_ref(v_msg_1079_);
v_a_1171_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1172_ = l_Lean_Exception_isInterrupt(v_a_1171_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; 
lean_inc(v_a_1171_);
v___x_1173_ = l_Lean_Exception_isRuntime(v_a_1171_);
v___y_1092_ = v_a_1151_;
v___y_1093_ = v_a_1171_;
v___y_1094_ = v___x_1173_;
goto v___jp_1091_;
}
else
{
v___y_1092_ = v_a_1151_;
v___y_1093_ = v_a_1171_;
v___y_1094_ = v___x_1172_;
goto v___jp_1091_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v___x_1149_);
lean_dec_ref_known(v___x_1138_, 2);
lean_dec(v___x_1135_);
lean_dec(v_expectedType_x3f_1081_);
lean_dec_ref(v_initialState_1080_);
lean_dec_ref(v_msg_1079_);
v_a_1174_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1150_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1150_);
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
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_expectedType_x3f_1081_);
lean_dec_ref(v_initialState_1080_);
lean_dec_ref(v_msg_1079_);
lean_dec(v_tac_1078_);
v_a_1182_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1133_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1133_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v___x_1191_; 
lean_dec(v_a_1115_);
lean_dec(v_expectedType_x3f_1081_);
lean_dec_ref(v_initialState_1080_);
lean_dec_ref(v_msg_1079_);
lean_dec(v_tac_1078_);
if (v_isShared_1130_ == 0)
{
v___x_1191_ = v___x_1129_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1127_);
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
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_expectedType_x3f_1081_);
lean_dec_ref(v_initialState_1080_);
lean_dec_ref(v_msg_1079_);
lean_dec(v_tac_1078_);
v_a_1196_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1114_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1114_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
v___jp_1091_:
{
if (v___y_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref(v___y_1093_);
v___x_1095_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_1092_, v___y_1094_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1103_; 
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; 
v_unused_1104_ = lean_ctor_get(v___x_1095_, 0);
lean_dec(v_unused_1104_);
v___x_1097_ = v___x_1095_;
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
else
{
lean_dec(v___x_1095_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_box(0);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1095_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1095_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v___x_1113_; 
lean_dec_ref(v___y_1092_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___y_1093_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object* v_tac_1204_, lean_object* v_msg_1205_, lean_object* v_initialState_1206_, lean_object* v_expectedType_x3f_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_tac_1204_, v_msg_1205_, v_initialState_1206_, v_expectedType_x3f_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__0));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* v_targetKind_1227_, lean_object* v_invalidTactic_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_targetKind_1227_);
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_indentD(v_invalidTactic_1228_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__0));
v___x_1239_ = l_Lean_stringToMessageData(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__2));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object* v_e_1255_, uint8_t v_useRefine_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___x_1267_; 
lean_inc_ref(v_e_1255_);
v___x_1267_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_tac_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
if (v_useRefine_1256_ == 0)
{
lean_object* v_ref_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_ref_1283_ = lean_ctor_get(v___y_1259_, 5);
v___x_1284_ = l_Lean_SourceInfo_fromRef(v_ref_1283_, v_useRefine_1256_);
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__4));
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__5));
lean_inc(v___x_1284_);
v___x_1287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1284_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
v___x_1288_ = l_Lean_Syntax_node2(v___x_1284_, v___x_1286_, v___x_1287_, v_a_1268_);
v_tac_1270_ = v___x_1288_;
v___y_1271_ = v___y_1257_;
v___y_1272_ = v___y_1258_;
v___y_1273_ = v___y_1259_;
v___y_1274_ = v___y_1260_;
goto v___jp_1269_;
}
else
{
lean_object* v_ref_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_ref_1289_ = lean_ctor_get(v___y_1259_, 5);
v___x_1290_ = 0;
v___x_1291_ = l_Lean_SourceInfo_fromRef(v_ref_1289_, v___x_1290_);
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__6));
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__7));
lean_inc(v___x_1291_);
v___x_1294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1292_);
v___x_1295_ = l_Lean_Syntax_node2(v___x_1291_, v___x_1293_, v___x_1294_, v_a_1268_);
v_tac_1270_ = v___x_1295_;
v___y_1271_ = v___y_1257_;
v___y_1272_ = v___y_1258_;
v___y_1273_ = v___y_1259_;
v___y_1274_ = v___y_1260_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = l_Lean_MessageData_ofExpr(v_e_1255_);
v___x_1276_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1275_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (v_useRefine_1256_ == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__1);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_a_1277_);
v___y_1263_ = v_tac_1270_;
v___y_1264_ = v___x_1279_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1280_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1276_);
v___x_1281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___closed__3);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_a_1280_);
v___y_1263_ = v_tac_1270_;
v___y_1264_ = v___x_1282_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_e_1255_);
v_a_1296_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1267_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1267_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___y_1263_);
lean_ctor_set(v___x_1265_, 1, v___y_1264_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object* v_e_1304_, lean_object* v_useRefine_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_useRefine_boxed_1311_; lean_object* v_res_1312_; 
v_useRefine_boxed_1311_ = lean_unbox(v_useRefine_1305_);
v_res_1312_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(v_e_1304_, v_useRefine_boxed_1311_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* v_e_1313_, uint8_t v_useRefine_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v_fileName_1321_; lean_object* v_fileMap_1322_; lean_object* v_options_1323_; lean_object* v_currRecDepth_1324_; lean_object* v_ref_1325_; lean_object* v_currNamespace_1326_; lean_object* v_openDecls_1327_; lean_object* v_initHeartbeats_1328_; lean_object* v_maxHeartbeats_1329_; lean_object* v_quotContext_1330_; lean_object* v_currMacroScope_1331_; lean_object* v_cancelTk_x3f_1332_; uint8_t v_suppressElabErrors_1333_; lean_object* v_inheritedTraceOptions_1334_; lean_object* v_env_1335_; lean_object* v___x_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v_fileName_1344_; lean_object* v_fileMap_1345_; lean_object* v_currRecDepth_1346_; lean_object* v_ref_1347_; lean_object* v_currNamespace_1348_; lean_object* v_openDecls_1349_; lean_object* v_initHeartbeats_1350_; lean_object* v_maxHeartbeats_1351_; lean_object* v_quotContext_1352_; lean_object* v_currMacroScope_1353_; lean_object* v_cancelTk_x3f_1354_; uint8_t v_suppressElabErrors_1355_; lean_object* v_inheritedTraceOptions_1356_; lean_object* v___y_1357_; uint8_t v___y_1363_; uint8_t v___x_1384_; 
v___x_1320_ = lean_st_ref_get(v_a_1318_);
v_fileName_1321_ = lean_ctor_get(v_a_1317_, 0);
v_fileMap_1322_ = lean_ctor_get(v_a_1317_, 1);
v_options_1323_ = lean_ctor_get(v_a_1317_, 2);
v_currRecDepth_1324_ = lean_ctor_get(v_a_1317_, 3);
v_ref_1325_ = lean_ctor_get(v_a_1317_, 5);
v_currNamespace_1326_ = lean_ctor_get(v_a_1317_, 6);
v_openDecls_1327_ = lean_ctor_get(v_a_1317_, 7);
v_initHeartbeats_1328_ = lean_ctor_get(v_a_1317_, 8);
v_maxHeartbeats_1329_ = lean_ctor_get(v_a_1317_, 9);
v_quotContext_1330_ = lean_ctor_get(v_a_1317_, 10);
v_currMacroScope_1331_ = lean_ctor_get(v_a_1317_, 11);
v_cancelTk_x3f_1332_ = lean_ctor_get(v_a_1317_, 12);
v_suppressElabErrors_1333_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1334_ = lean_ctor_get(v_a_1317_, 13);
v_env_1335_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_ref(v_env_1335_);
lean_dec(v___x_1320_);
v___x_1336_ = lean_box(v_useRefine_1314_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1337_, 0, v_e_1313_);
lean_closure_set(v___f_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_pp_mvars;
v___x_1339_ = 0;
lean_inc_ref(v_options_1323_);
v___x_1340_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_1323_, v___x_1338_, v___x_1339_);
v___x_1341_ = l_Lean_diagnostics;
v___x_1342_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_1340_, v___x_1341_);
v___x_1384_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1335_);
lean_dec_ref(v_env_1335_);
if (v___x_1384_ == 0)
{
if (v___x_1342_ == 0)
{
v_fileName_1344_ = v_fileName_1321_;
v_fileMap_1345_ = v_fileMap_1322_;
v_currRecDepth_1346_ = v_currRecDepth_1324_;
v_ref_1347_ = v_ref_1325_;
v_currNamespace_1348_ = v_currNamespace_1326_;
v_openDecls_1349_ = v_openDecls_1327_;
v_initHeartbeats_1350_ = v_initHeartbeats_1328_;
v_maxHeartbeats_1351_ = v_maxHeartbeats_1329_;
v_quotContext_1352_ = v_quotContext_1330_;
v_currMacroScope_1353_ = v_currMacroScope_1331_;
v_cancelTk_x3f_1354_ = v_cancelTk_x3f_1332_;
v_suppressElabErrors_1355_ = v_suppressElabErrors_1333_;
v_inheritedTraceOptions_1356_ = v_inheritedTraceOptions_1334_;
v___y_1357_ = v_a_1318_;
goto v___jp_1343_;
}
else
{
v___y_1363_ = v___x_1384_;
goto v___jp_1362_;
}
}
else
{
v___y_1363_ = v___x_1342_;
goto v___jp_1362_;
}
v___jp_1343_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = l_Lean_maxRecDepth;
v___x_1359_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_1340_, v___x_1358_);
lean_inc_ref(v_inheritedTraceOptions_1356_);
lean_inc(v_cancelTk_x3f_1354_);
lean_inc(v_currMacroScope_1353_);
lean_inc(v_quotContext_1352_);
lean_inc(v_maxHeartbeats_1351_);
lean_inc(v_initHeartbeats_1350_);
lean_inc(v_openDecls_1349_);
lean_inc(v_currNamespace_1348_);
lean_inc(v_ref_1347_);
lean_inc(v_currRecDepth_1346_);
lean_inc_ref(v_fileMap_1345_);
lean_inc_ref(v_fileName_1344_);
v___x_1360_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1360_, 0, v_fileName_1344_);
lean_ctor_set(v___x_1360_, 1, v_fileMap_1345_);
lean_ctor_set(v___x_1360_, 2, v___x_1340_);
lean_ctor_set(v___x_1360_, 3, v_currRecDepth_1346_);
lean_ctor_set(v___x_1360_, 4, v___x_1359_);
lean_ctor_set(v___x_1360_, 5, v_ref_1347_);
lean_ctor_set(v___x_1360_, 6, v_currNamespace_1348_);
lean_ctor_set(v___x_1360_, 7, v_openDecls_1349_);
lean_ctor_set(v___x_1360_, 8, v_initHeartbeats_1350_);
lean_ctor_set(v___x_1360_, 9, v_maxHeartbeats_1351_);
lean_ctor_set(v___x_1360_, 10, v_quotContext_1352_);
lean_ctor_set(v___x_1360_, 11, v_currMacroScope_1353_);
lean_ctor_set(v___x_1360_, 12, v_cancelTk_x3f_1354_);
lean_ctor_set(v___x_1360_, 13, v_inheritedTraceOptions_1356_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*14, v___x_1342_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*14 + 1, v_suppressElabErrors_1355_);
v___x_1361_ = l_Lean_Meta_withExposedNames___redArg(v___f_1337_, v_a_1315_, v_a_1316_, v___x_1360_, v___y_1357_);
lean_dec_ref_known(v___x_1360_, 14);
return v___x_1361_;
}
v___jp_1362_:
{
if (v___y_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v_env_1365_; lean_object* v_nextMacroScope_1366_; lean_object* v_ngen_1367_; lean_object* v_auxDeclNGen_1368_; lean_object* v_traceState_1369_; lean_object* v_messages_1370_; lean_object* v_infoState_1371_; lean_object* v_snapshotTasks_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1382_; 
v___x_1364_ = lean_st_ref_take(v_a_1318_);
v_env_1365_ = lean_ctor_get(v___x_1364_, 0);
v_nextMacroScope_1366_ = lean_ctor_get(v___x_1364_, 1);
v_ngen_1367_ = lean_ctor_get(v___x_1364_, 2);
v_auxDeclNGen_1368_ = lean_ctor_get(v___x_1364_, 3);
v_traceState_1369_ = lean_ctor_get(v___x_1364_, 4);
v_messages_1370_ = lean_ctor_get(v___x_1364_, 6);
v_infoState_1371_ = lean_ctor_get(v___x_1364_, 7);
v_snapshotTasks_1372_ = lean_ctor_get(v___x_1364_, 8);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1364_, 5);
lean_dec(v_unused_1383_);
v___x_1374_ = v___x_1364_;
v_isShared_1375_ = v_isSharedCheck_1382_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snapshotTasks_1372_);
lean_inc(v_infoState_1371_);
lean_inc(v_messages_1370_);
lean_inc(v_traceState_1369_);
lean_inc(v_auxDeclNGen_1368_);
lean_inc(v_ngen_1367_);
lean_inc(v_nextMacroScope_1366_);
lean_inc(v_env_1365_);
lean_dec(v___x_1364_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1382_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = l_Lean_Kernel_enableDiag(v_env_1365_, v___x_1342_);
v___x_1377_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 5, v___x_1377_);
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_nextMacroScope_1366_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_ngen_1367_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v_auxDeclNGen_1368_);
lean_ctor_set(v_reuseFailAlloc_1381_, 4, v_traceState_1369_);
lean_ctor_set(v_reuseFailAlloc_1381_, 5, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1381_, 6, v_messages_1370_);
lean_ctor_set(v_reuseFailAlloc_1381_, 7, v_infoState_1371_);
lean_ctor_set(v_reuseFailAlloc_1381_, 8, v_snapshotTasks_1372_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_st_ref_set(v_a_1318_, v___x_1379_);
v_fileName_1344_ = v_fileName_1321_;
v_fileMap_1345_ = v_fileMap_1322_;
v_currRecDepth_1346_ = v_currRecDepth_1324_;
v_ref_1347_ = v_ref_1325_;
v_currNamespace_1348_ = v_currNamespace_1326_;
v_openDecls_1349_ = v_openDecls_1327_;
v_initHeartbeats_1350_ = v_initHeartbeats_1328_;
v_maxHeartbeats_1351_ = v_maxHeartbeats_1329_;
v_quotContext_1352_ = v_quotContext_1330_;
v_currMacroScope_1353_ = v_currMacroScope_1331_;
v_cancelTk_x3f_1354_ = v_cancelTk_x3f_1332_;
v_suppressElabErrors_1355_ = v_suppressElabErrors_1333_;
v_inheritedTraceOptions_1356_ = v_inheritedTraceOptions_1334_;
v___y_1357_ = v_a_1318_;
goto v___jp_1343_;
}
}
}
else
{
v_fileName_1344_ = v_fileName_1321_;
v_fileMap_1345_ = v_fileMap_1322_;
v_currRecDepth_1346_ = v_currRecDepth_1324_;
v_ref_1347_ = v_ref_1325_;
v_currNamespace_1348_ = v_currNamespace_1326_;
v_openDecls_1349_ = v_openDecls_1327_;
v_initHeartbeats_1350_ = v_initHeartbeats_1328_;
v_maxHeartbeats_1351_ = v_maxHeartbeats_1329_;
v_quotContext_1352_ = v_quotContext_1330_;
v_currMacroScope_1353_ = v_currMacroScope_1331_;
v_cancelTk_x3f_1354_ = v_cancelTk_x3f_1332_;
v_suppressElabErrors_1355_ = v_suppressElabErrors_1333_;
v_inheritedTraceOptions_1356_ = v_inheritedTraceOptions_1334_;
v___y_1357_ = v_a_1318_;
goto v___jp_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* v_e_1385_, lean_object* v_useRefine_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
uint8_t v_useRefine_boxed_1392_; lean_object* v_res_1393_; 
v_useRefine_boxed_1392_ = lean_unbox(v_useRefine_1386_);
v_res_1393_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1385_, v_useRefine_boxed_1392_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(lean_object* v_as_1397_, size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_b_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_lt(v_i_1399_, v_sz_1398_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_b_1400_);
return v___x_1407_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_array_uget_borrowed(v_as_1397_, v_i_1399_);
lean_inc(v_a_1408_);
v___x_1409_ = l_Lean_MVarId_getType(v_a_1408_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__1___redArg(v_a_1410_, v___y_1402_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___boxed), 6, 1);
lean_closure_set(v___x_1413_, 0, v_a_1412_);
v___x_1414_ = l_Lean_Meta_withExposedNames___redArg(v___x_1413_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___closed__1));
v___x_1417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v_a_1415_);
v___x_1418_ = l_Std_Format_defWidth;
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = l_Std_Format_pretty(v___x_1417_, v___x_1418_, v___x_1419_, v___x_1419_);
v___x_1421_ = lean_string_append(v_b_1400_, v___x_1420_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1399_, v___x_1422_);
v_i_1399_ = v___x_1423_;
v_b_1400_ = v___x_1421_;
goto _start;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_b_1400_);
v_a_1425_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1414_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1414_);
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
lean_dec_ref(v_b_1400_);
v_a_1433_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1411_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1411_);
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
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_b_1400_);
v_a_1441_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1409_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1409_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg___boxed(lean_object* v_as_1449_, lean_object* v_sz_1450_, lean_object* v_i_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
size_t v_sz_boxed_1458_; size_t v_i_boxed_1459_; lean_object* v_res_1460_; 
v_sz_boxed_1458_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1459_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1449_, v_sz_boxed_1458_, v_i_boxed_1459_, v_b_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_as_1449_);
return v_res_1460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__2));
v___x_1466_ = l_Lean_stringToMessageData(v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__5));
v___x_1470_ = l_Lean_stringToMessageData(v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t v_addSubgoalsMsg_1472_, lean_object* v_checkState_x3f_1473_, lean_object* v_e_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v_postInfo_x3f_1487_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___y_1514_; uint8_t v___y_1515_; lean_object* v___x_1600_; lean_object* v_fileName_1601_; lean_object* v_fileMap_1602_; lean_object* v_options_1603_; lean_object* v_currRecDepth_1604_; lean_object* v_ref_1605_; lean_object* v_currNamespace_1606_; lean_object* v_openDecls_1607_; lean_object* v_initHeartbeats_1608_; lean_object* v_maxHeartbeats_1609_; lean_object* v_quotContext_1610_; lean_object* v_currMacroScope_1611_; lean_object* v_cancelTk_x3f_1612_; uint8_t v_suppressElabErrors_1613_; lean_object* v_inheritedTraceOptions_1614_; lean_object* v_env_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v_fileName_1622_; lean_object* v_fileMap_1623_; lean_object* v_currRecDepth_1624_; lean_object* v_ref_1625_; lean_object* v_currNamespace_1626_; lean_object* v_openDecls_1627_; lean_object* v_initHeartbeats_1628_; lean_object* v_maxHeartbeats_1629_; lean_object* v_quotContext_1630_; lean_object* v_currMacroScope_1631_; lean_object* v_cancelTk_x3f_1632_; uint8_t v_suppressElabErrors_1633_; lean_object* v_inheritedTraceOptions_1634_; lean_object* v___y_1635_; uint8_t v___y_1654_; uint8_t v___x_1675_; 
v___x_1600_ = lean_st_ref_get(v_a_1482_);
v_fileName_1601_ = lean_ctor_get(v_a_1481_, 0);
v_fileMap_1602_ = lean_ctor_get(v_a_1481_, 1);
v_options_1603_ = lean_ctor_get(v_a_1481_, 2);
v_currRecDepth_1604_ = lean_ctor_get(v_a_1481_, 3);
v_ref_1605_ = lean_ctor_get(v_a_1481_, 5);
v_currNamespace_1606_ = lean_ctor_get(v_a_1481_, 6);
v_openDecls_1607_ = lean_ctor_get(v_a_1481_, 7);
v_initHeartbeats_1608_ = lean_ctor_get(v_a_1481_, 8);
v_maxHeartbeats_1609_ = lean_ctor_get(v_a_1481_, 9);
v_quotContext_1610_ = lean_ctor_get(v_a_1481_, 10);
v_currMacroScope_1611_ = lean_ctor_get(v_a_1481_, 11);
v_cancelTk_x3f_1612_ = lean_ctor_get(v_a_1481_, 12);
v_suppressElabErrors_1613_ = lean_ctor_get_uint8(v_a_1481_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1614_ = lean_ctor_get(v_a_1481_, 13);
v_env_1615_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1615_);
lean_dec(v___x_1600_);
v___x_1616_ = l_Lean_pp_mvars;
v___x_1617_ = 0;
lean_inc_ref(v_options_1603_);
v___x_1618_ = l_Lean_Option_set___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__0(v_options_1603_, v___x_1616_, v___x_1617_);
v___x_1619_ = l_Lean_diagnostics;
v___x_1620_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v___x_1618_, v___x_1619_);
v___x_1675_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1615_);
lean_dec_ref(v_env_1615_);
if (v___x_1675_ == 0)
{
if (v___x_1620_ == 0)
{
v_fileName_1622_ = v_fileName_1601_;
v_fileMap_1623_ = v_fileMap_1602_;
v_currRecDepth_1624_ = v_currRecDepth_1604_;
v_ref_1625_ = v_ref_1605_;
v_currNamespace_1626_ = v_currNamespace_1606_;
v_openDecls_1627_ = v_openDecls_1607_;
v_initHeartbeats_1628_ = v_initHeartbeats_1608_;
v_maxHeartbeats_1629_ = v_maxHeartbeats_1609_;
v_quotContext_1630_ = v_quotContext_1610_;
v_currMacroScope_1631_ = v_currMacroScope_1611_;
v_cancelTk_x3f_1632_ = v_cancelTk_x3f_1612_;
v_suppressElabErrors_1633_ = v_suppressElabErrors_1613_;
v_inheritedTraceOptions_1634_ = v_inheritedTraceOptions_1614_;
v___y_1635_ = v_a_1482_;
goto v___jp_1621_;
}
else
{
v___y_1654_ = v___x_1675_;
goto v___jp_1653_;
}
}
else
{
v___y_1654_ = v___x_1620_;
goto v___jp_1653_;
}
v___jp_1484_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___y_1486_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___y_1485_);
v___x_1492_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1489_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v_postInfo_x3f_1487_);
lean_ctor_set(v___x_1492_, 3, v___x_1490_);
lean_ctor_set(v___x_1492_, 4, v___x_1491_);
lean_ctor_set(v___x_1492_, 5, v___x_1490_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
v___jp_1495_:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_box(0);
v___y_1485_ = v___y_1497_;
v___y_1486_ = v___y_1496_;
v_postInfo_x3f_1487_ = v___x_1498_;
goto v___jp_1484_;
}
v___jp_1499_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_inc_ref(v___y_1502_);
v___x_1503_ = l_Lean_stringToMessageData(v___y_1502_);
lean_inc_ref(v___y_1501_);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___y_1501_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__3);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_1506_, v___y_1500_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
v___jp_1510_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(v_e_1474_, v___y_1515_, v_a_1479_, v_a_1480_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1591_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1591_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1591_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
if (lean_obj_tag(v_checkState_x3f_1473_) == 1)
{
lean_object* v_fst_1521_; lean_object* v_snd_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1519_);
v_fst_1521_ = lean_ctor_get(v_a_1517_, 0);
v_snd_1522_ = lean_ctor_get(v_a_1517_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_a_1517_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1524_ = v_a_1517_;
v_isShared_1525_ = v_isSharedCheck_1574_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_snd_1522_);
lean_inc(v_fst_1521_);
lean_dec(v_a_1517_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1574_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_val_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_val_1526_ = lean_ctor_get(v_checkState_x3f_1473_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v_checkState_x3f_1473_, 1);
v___x_1527_ = lean_box(0);
lean_inc(v_snd_1522_);
v___x_1528_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_1521_, v_snd_1522_, v_val_1526_, v___x_1527_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
if (lean_obj_tag(v_a_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1556_; 
lean_del_object(v___x_1524_);
lean_dec(v_snd_1522_);
v_val_1530_ = lean_ctor_get(v_a_1529_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_a_1529_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1532_ = v_a_1529_;
v_isShared_1533_ = v_isSharedCheck_1556_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v_a_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1556_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
if (v_addSubgoalsMsg_1472_ == 0)
{
lean_object* v_fst_1534_; lean_object* v_snd_1535_; 
lean_del_object(v___x_1532_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1511_);
v_fst_1534_ = lean_ctor_get(v_val_1530_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_val_1530_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_val_1530_);
v___y_1496_ = v_fst_1534_;
v___y_1497_ = v_snd_1535_;
goto v___jp_1495_;
}
else
{
if (v___y_1514_ == 0)
{
lean_object* v_fst_1536_; lean_object* v_snd_1537_; lean_object* v___x_1538_; size_t v_sz_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_fst_1536_ = lean_ctor_get(v_val_1530_, 0);
lean_inc(v_fst_1536_);
v_snd_1537_ = lean_ctor_get(v_val_1530_, 1);
lean_inc(v_snd_1537_);
lean_dec(v_val_1530_);
v___x_1538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__4));
v_sz_1539_ = lean_array_size(v___y_1513_);
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v___y_1513_, v_sz_1539_, v___x_1540_, v___x_1538_, v_a_1479_, v_a_1480_, v___y_1511_, v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec_ref(v___y_1513_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_a_1542_);
v___x_1544_ = v___x_1532_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
v___y_1485_ = v_snd_1537_;
v___y_1486_ = v_fst_1536_;
v_postInfo_x3f_1487_ = v___x_1544_;
goto v___jp_1484_;
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_snd_1537_);
lean_dec(v_fst_1536_);
lean_del_object(v___x_1532_);
v_a_1546_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1541_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1541_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_fst_1554_; lean_object* v_snd_1555_; 
lean_del_object(v___x_1532_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1511_);
v_fst_1554_ = lean_ctor_get(v_val_1530_, 0);
lean_inc(v_fst_1554_);
v_snd_1555_ = lean_ctor_get(v_val_1530_, 1);
lean_inc(v_snd_1555_);
lean_dec(v_val_1530_);
v___y_1496_ = v_fst_1554_;
v___y_1497_ = v_snd_1555_;
goto v___jp_1495_;
}
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_dec(v_a_1529_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1511_);
v___x_1557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 7);
lean_ctor_set(v___x_1524_, 0, v___x_1557_);
v___x_1559_ = v___x_1524_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_snd_1522_);
v___x_1559_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__6);
if (v___y_1515_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_1500_ = v___x_1561_;
v___y_1501_ = v___x_1562_;
v___y_1502_ = v___x_1563_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__7));
v___y_1500_ = v___x_1561_;
v___y_1501_ = v___x_1562_;
v___y_1502_ = v___x_1564_;
goto v___jp_1499_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_del_object(v___x_1524_);
lean_dec(v_snd_1522_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1511_);
v_a_1566_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1528_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1528_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_object* v_fst_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1511_);
lean_dec(v_checkState_x3f_1473_);
v_fst_1575_ = lean_ctor_get(v_a_1517_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_a_1517_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v_a_1517_, 1);
lean_dec(v_unused_1590_);
v___x_1577_ = v_a_1517_;
v_isShared_1578_ = v_isSharedCheck_1589_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_fst_1575_);
lean_dec(v_a_1517_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1589_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v_fst_1575_);
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_fst_1575_);
v___x_1581_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
lean_ctor_set(v___x_1583_, 2, v___x_1582_);
lean_ctor_set(v___x_1583_, 3, v___x_1582_);
lean_ctor_set(v___x_1583_, 4, v___x_1582_);
lean_ctor_set(v___x_1583_, 5, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1584_);
v___x_1586_ = v___x_1519_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___y_1511_);
lean_dec(v_checkState_x3f_1473_);
v_a_1592_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1516_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1516_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
v___jp_1621_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1636_ = l_Lean_maxRecDepth;
v___x_1637_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__2(v___x_1618_, v___x_1636_);
lean_inc_ref(v_inheritedTraceOptions_1634_);
lean_inc(v_cancelTk_x3f_1632_);
lean_inc(v_currMacroScope_1631_);
lean_inc(v_quotContext_1630_);
lean_inc(v_maxHeartbeats_1629_);
lean_inc(v_initHeartbeats_1628_);
lean_inc(v_openDecls_1627_);
lean_inc(v_currNamespace_1626_);
lean_inc(v_ref_1625_);
lean_inc(v_currRecDepth_1624_);
lean_inc_ref(v_fileMap_1623_);
lean_inc_ref(v_fileName_1622_);
v___x_1638_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1638_, 0, v_fileName_1622_);
lean_ctor_set(v___x_1638_, 1, v_fileMap_1623_);
lean_ctor_set(v___x_1638_, 2, v___x_1618_);
lean_ctor_set(v___x_1638_, 3, v_currRecDepth_1624_);
lean_ctor_set(v___x_1638_, 4, v___x_1637_);
lean_ctor_set(v___x_1638_, 5, v_ref_1625_);
lean_ctor_set(v___x_1638_, 6, v_currNamespace_1626_);
lean_ctor_set(v___x_1638_, 7, v_openDecls_1627_);
lean_ctor_set(v___x_1638_, 8, v_initHeartbeats_1628_);
lean_ctor_set(v___x_1638_, 9, v_maxHeartbeats_1629_);
lean_ctor_set(v___x_1638_, 10, v_quotContext_1630_);
lean_ctor_set(v___x_1638_, 11, v_currMacroScope_1631_);
lean_ctor_set(v___x_1638_, 12, v_cancelTk_x3f_1632_);
lean_ctor_set(v___x_1638_, 13, v_inheritedTraceOptions_1634_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*14, v___x_1620_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*14 + 1, v_suppressElabErrors_1633_);
lean_inc_ref(v_e_1474_);
v___x_1639_ = l_Lean_Meta_getMVars(v_e_1474_, v_a_1479_, v_a_1480_, v___x_1638_, v___y_1635_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = lean_array_get_size(v_a_1640_);
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_nat_dec_eq(v___x_1641_, v___x_1642_);
if (v___x_1643_ == 0)
{
uint8_t v___x_1644_; 
v___x_1644_ = 1;
v___y_1511_ = v___x_1638_;
v___y_1512_ = v___y_1635_;
v___y_1513_ = v_a_1640_;
v___y_1514_ = v___x_1643_;
v___y_1515_ = v___x_1644_;
goto v___jp_1510_;
}
else
{
v___y_1511_ = v___x_1638_;
v___y_1512_ = v___y_1635_;
v___y_1513_ = v_a_1640_;
v___y_1514_ = v___x_1643_;
v___y_1515_ = v___x_1617_;
goto v___jp_1510_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref_known(v___x_1638_, 14);
lean_dec_ref(v_e_1474_);
lean_dec(v_checkState_x3f_1473_);
v_a_1645_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1639_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1639_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
v___jp_1653_:
{
if (v___y_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v_env_1656_; lean_object* v_nextMacroScope_1657_; lean_object* v_ngen_1658_; lean_object* v_auxDeclNGen_1659_; lean_object* v_traceState_1660_; lean_object* v_messages_1661_; lean_object* v_infoState_1662_; lean_object* v_snapshotTasks_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1673_; 
v___x_1655_ = lean_st_ref_take(v_a_1482_);
v_env_1656_ = lean_ctor_get(v___x_1655_, 0);
v_nextMacroScope_1657_ = lean_ctor_get(v___x_1655_, 1);
v_ngen_1658_ = lean_ctor_get(v___x_1655_, 2);
v_auxDeclNGen_1659_ = lean_ctor_get(v___x_1655_, 3);
v_traceState_1660_ = lean_ctor_get(v___x_1655_, 4);
v_messages_1661_ = lean_ctor_get(v___x_1655_, 6);
v_infoState_1662_ = lean_ctor_get(v___x_1655_, 7);
v_snapshotTasks_1663_ = lean_ctor_get(v___x_1655_, 8);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1655_, 5);
lean_dec(v_unused_1674_);
v___x_1665_ = v___x_1655_;
v_isShared_1666_ = v_isSharedCheck_1673_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_snapshotTasks_1663_);
lean_inc(v_infoState_1662_);
lean_inc(v_messages_1661_);
lean_inc(v_traceState_1660_);
lean_inc(v_auxDeclNGen_1659_);
lean_inc(v_ngen_1658_);
lean_inc(v_nextMacroScope_1657_);
lean_inc(v_env_1656_);
lean_dec(v___x_1655_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1673_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = l_Lean_Kernel_enableDiag(v_env_1656_, v___x_1620_);
v___x_1668_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2, &l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 5, v___x_1668_);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_nextMacroScope_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_ngen_1658_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_auxDeclNGen_1659_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v_traceState_1660_);
lean_ctor_set(v_reuseFailAlloc_1672_, 5, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1672_, 6, v_messages_1661_);
lean_ctor_set(v_reuseFailAlloc_1672_, 7, v_infoState_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 8, v_snapshotTasks_1663_);
v___x_1670_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_st_ref_set(v_a_1482_, v___x_1670_);
v_fileName_1622_ = v_fileName_1601_;
v_fileMap_1623_ = v_fileMap_1602_;
v_currRecDepth_1624_ = v_currRecDepth_1604_;
v_ref_1625_ = v_ref_1605_;
v_currNamespace_1626_ = v_currNamespace_1606_;
v_openDecls_1627_ = v_openDecls_1607_;
v_initHeartbeats_1628_ = v_initHeartbeats_1608_;
v_maxHeartbeats_1629_ = v_maxHeartbeats_1609_;
v_quotContext_1630_ = v_quotContext_1610_;
v_currMacroScope_1631_ = v_currMacroScope_1611_;
v_cancelTk_x3f_1632_ = v_cancelTk_x3f_1612_;
v_suppressElabErrors_1633_ = v_suppressElabErrors_1613_;
v_inheritedTraceOptions_1634_ = v_inheritedTraceOptions_1614_;
v___y_1635_ = v_a_1482_;
goto v___jp_1621_;
}
}
}
else
{
v_fileName_1622_ = v_fileName_1601_;
v_fileMap_1623_ = v_fileMap_1602_;
v_currRecDepth_1624_ = v_currRecDepth_1604_;
v_ref_1625_ = v_ref_1605_;
v_currNamespace_1626_ = v_currNamespace_1606_;
v_openDecls_1627_ = v_openDecls_1607_;
v_initHeartbeats_1628_ = v_initHeartbeats_1608_;
v_maxHeartbeats_1629_ = v_maxHeartbeats_1609_;
v_quotContext_1630_ = v_quotContext_1610_;
v_currMacroScope_1631_ = v_currMacroScope_1611_;
v_cancelTk_x3f_1632_ = v_cancelTk_x3f_1612_;
v_suppressElabErrors_1633_ = v_suppressElabErrors_1613_;
v_inheritedTraceOptions_1634_ = v_inheritedTraceOptions_1614_;
v___y_1635_ = v_a_1482_;
goto v___jp_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* v_addSubgoalsMsg_1676_, lean_object* v_checkState_x3f_1677_, lean_object* v_e_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1688_; lean_object* v_res_1689_; 
v_addSubgoalsMsg_boxed_1688_ = lean_unbox(v_addSubgoalsMsg_1676_);
v_res_1689_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_boxed_1688_, v_checkState_x3f_1677_, v_e_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object* v_as_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___redArg(v_as_1690_, v_sz_1691_, v_i_1692_, v_b_1693_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object* v_as_1704_, lean_object* v_sz_1705_, lean_object* v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1705_);
lean_dec(v_sz_1705_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(v_as_1704_, v_sz_boxed_1717_, v_i_boxed_1718_, v_b_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v_as_1704_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1720_, lean_object* v_msgData_1721_, uint8_t v_severity_1722_, uint8_t v_isSilent_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___y_1730_; uint8_t v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; uint8_t v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1768_; lean_object* v___y_1769_; uint8_t v___y_1770_; uint8_t v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1802_; lean_object* v___y_1803_; uint8_t v___y_1804_; lean_object* v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; uint8_t v___x_1813_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; uint8_t v___y_1820_; uint8_t v___y_1821_; uint8_t v___y_1823_; uint8_t v___x_1838_; 
v___x_1813_ = 2;
v___x_1838_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1722_, v___x_1813_);
if (v___x_1838_ == 0)
{
v___y_1823_ = v___x_1838_;
goto v___jp_1822_;
}
else
{
uint8_t v___x_1839_; 
lean_inc_ref(v_msgData_1721_);
v___x_1839_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1721_);
v___y_1823_ = v___x_1839_;
goto v___jp_1822_;
}
v___jp_1729_:
{
lean_object* v___x_1739_; lean_object* v_currNamespace_1740_; lean_object* v_openDecls_1741_; lean_object* v_env_1742_; lean_object* v_nextMacroScope_1743_; lean_object* v_ngen_1744_; lean_object* v_auxDeclNGen_1745_; lean_object* v_traceState_1746_; lean_object* v_cache_1747_; lean_object* v_messages_1748_; lean_object* v_infoState_1749_; lean_object* v_snapshotTasks_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1764_; 
v___x_1739_ = lean_st_ref_take(v___y_1738_);
v_currNamespace_1740_ = lean_ctor_get(v___y_1737_, 6);
v_openDecls_1741_ = lean_ctor_get(v___y_1737_, 7);
v_env_1742_ = lean_ctor_get(v___x_1739_, 0);
v_nextMacroScope_1743_ = lean_ctor_get(v___x_1739_, 1);
v_ngen_1744_ = lean_ctor_get(v___x_1739_, 2);
v_auxDeclNGen_1745_ = lean_ctor_get(v___x_1739_, 3);
v_traceState_1746_ = lean_ctor_get(v___x_1739_, 4);
v_cache_1747_ = lean_ctor_get(v___x_1739_, 5);
v_messages_1748_ = lean_ctor_get(v___x_1739_, 6);
v_infoState_1749_ = lean_ctor_get(v___x_1739_, 7);
v_snapshotTasks_1750_ = lean_ctor_get(v___x_1739_, 8);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1752_ = v___x_1739_;
v_isShared_1753_ = v_isSharedCheck_1764_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_snapshotTasks_1750_);
lean_inc(v_infoState_1749_);
lean_inc(v_messages_1748_);
lean_inc(v_cache_1747_);
lean_inc(v_traceState_1746_);
lean_inc(v_auxDeclNGen_1745_);
lean_inc(v_ngen_1744_);
lean_inc(v_nextMacroScope_1743_);
lean_inc(v_env_1742_);
lean_dec(v___x_1739_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1764_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_inc(v_openDecls_1741_);
lean_inc(v_currNamespace_1740_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_currNamespace_1740_);
lean_ctor_set(v___x_1754_, 1, v_openDecls_1741_);
v___x_1755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___y_1736_);
lean_inc_ref(v___y_1733_);
lean_inc_ref(v___y_1732_);
v___x_1756_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1756_, 0, v___y_1732_);
lean_ctor_set(v___x_1756_, 1, v___y_1735_);
lean_ctor_set(v___x_1756_, 2, v___y_1730_);
lean_ctor_set(v___x_1756_, 3, v___y_1733_);
lean_ctor_set(v___x_1756_, 4, v___x_1755_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*5, v___y_1734_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*5 + 1, v___y_1731_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*5 + 2, v_isSilent_1723_);
v___x_1757_ = l_Lean_MessageLog_add(v___x_1756_, v_messages_1748_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 6, v___x_1757_);
v___x_1759_ = v___x_1752_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_env_1742_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_nextMacroScope_1743_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_ngen_1744_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_auxDeclNGen_1745_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_traceState_1746_);
lean_ctor_set(v_reuseFailAlloc_1763_, 5, v_cache_1747_);
lean_ctor_set(v_reuseFailAlloc_1763_, 6, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 7, v_infoState_1749_);
lean_ctor_set(v_reuseFailAlloc_1763_, 8, v_snapshotTasks_1750_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_st_ref_set(v___y_1738_, v___x_1759_);
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
v___jp_1765_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1789_; 
v___x_1774_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1721_);
v___x_1775_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_1774_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_inc_ref_n(v___y_1772_, 2);
v___x_1780_ = l_Lean_FileMap_toPosition(v___y_1772_, v___y_1769_);
lean_dec(v___y_1769_);
v___x_1781_ = l_Lean_FileMap_toPosition(v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
if (v___y_1771_ == 0)
{
lean_del_object(v___x_1778_);
lean_dec_ref(v___y_1766_);
v___y_1730_ = v___x_1782_;
v___y_1731_ = v___y_1768_;
v___y_1732_ = v___y_1767_;
v___y_1733_ = v___x_1783_;
v___y_1734_ = v___y_1770_;
v___y_1735_ = v___x_1780_;
v___y_1736_ = v_a_1776_;
v___y_1737_ = v___y_1726_;
v___y_1738_ = v___y_1727_;
goto v___jp_1729_;
}
else
{
uint8_t v___x_1784_; 
lean_inc(v_a_1776_);
v___x_1784_ = l_Lean_MessageData_hasTag(v___y_1766_, v_a_1776_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec_ref_known(v___x_1782_, 1);
lean_dec_ref(v___x_1780_);
lean_dec(v_a_1776_);
v___x_1785_ = lean_box(0);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1785_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_del_object(v___x_1778_);
v___y_1730_ = v___x_1782_;
v___y_1731_ = v___y_1768_;
v___y_1732_ = v___y_1767_;
v___y_1733_ = v___x_1783_;
v___y_1734_ = v___y_1770_;
v___y_1735_ = v___x_1780_;
v___y_1736_ = v_a_1776_;
v___y_1737_ = v___y_1726_;
v___y_1738_ = v___y_1727_;
goto v___jp_1729_;
}
}
}
}
v___jp_1790_:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Syntax_getTailPos_x3f(v___y_1794_, v___y_1795_);
lean_dec(v___y_1794_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_inc(v___y_1798_);
v___y_1766_ = v___y_1791_;
v___y_1767_ = v___y_1793_;
v___y_1768_ = v___y_1792_;
v___y_1769_ = v___y_1798_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1797_;
v___y_1772_ = v___y_1796_;
v___y_1773_ = v___y_1798_;
goto v___jp_1765_;
}
else
{
lean_object* v_val_1800_; 
v_val_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_val_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___y_1766_ = v___y_1791_;
v___y_1767_ = v___y_1793_;
v___y_1768_ = v___y_1792_;
v___y_1769_ = v___y_1798_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1797_;
v___y_1772_ = v___y_1796_;
v___y_1773_ = v_val_1800_;
goto v___jp_1765_;
}
}
v___jp_1801_:
{
lean_object* v_ref_1809_; lean_object* v___x_1810_; 
v_ref_1809_ = l_Lean_replaceRef(v_ref_1720_, v___y_1805_);
v___x_1810_ = l_Lean_Syntax_getPos_x3f(v_ref_1809_, v___y_1804_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___y_1791_ = v___y_1802_;
v___y_1792_ = v___y_1808_;
v___y_1793_ = v___y_1803_;
v___y_1794_ = v_ref_1809_;
v___y_1795_ = v___y_1804_;
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1806_;
v___y_1798_ = v___x_1811_;
goto v___jp_1790_;
}
else
{
lean_object* v_val_1812_; 
v_val_1812_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_val_1812_);
lean_dec_ref_known(v___x_1810_, 1);
v___y_1791_ = v___y_1802_;
v___y_1792_ = v___y_1808_;
v___y_1793_ = v___y_1803_;
v___y_1794_ = v_ref_1809_;
v___y_1795_ = v___y_1804_;
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1806_;
v___y_1798_ = v_val_1812_;
goto v___jp_1790_;
}
}
v___jp_1814_:
{
if (v___y_1821_ == 0)
{
v___y_1802_ = v___y_1817_;
v___y_1803_ = v___y_1815_;
v___y_1804_ = v___y_1820_;
v___y_1805_ = v___y_1816_;
v___y_1806_ = v___y_1819_;
v___y_1807_ = v___y_1818_;
v___y_1808_ = v_severity_1722_;
goto v___jp_1801_;
}
else
{
v___y_1802_ = v___y_1817_;
v___y_1803_ = v___y_1815_;
v___y_1804_ = v___y_1820_;
v___y_1805_ = v___y_1816_;
v___y_1806_ = v___y_1819_;
v___y_1807_ = v___y_1818_;
v___y_1808_ = v___x_1813_;
goto v___jp_1801_;
}
}
v___jp_1822_:
{
if (v___y_1823_ == 0)
{
lean_object* v_fileName_1824_; lean_object* v_fileMap_1825_; lean_object* v_options_1826_; lean_object* v_ref_1827_; uint8_t v_suppressElabErrors_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___f_1831_; uint8_t v___x_1832_; uint8_t v___x_1833_; 
v_fileName_1824_ = lean_ctor_get(v___y_1726_, 0);
v_fileMap_1825_ = lean_ctor_get(v___y_1726_, 1);
v_options_1826_ = lean_ctor_get(v___y_1726_, 2);
v_ref_1827_ = lean_ctor_get(v___y_1726_, 5);
v_suppressElabErrors_1828_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*14 + 1);
v___x_1829_ = lean_box(v___y_1823_);
v___x_1830_ = lean_box(v_suppressElabErrors_1828_);
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1831_, 0, v___x_1829_);
lean_closure_set(v___f_1831_, 1, v___x_1830_);
v___x_1832_ = 1;
v___x_1833_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1722_, v___x_1832_);
if (v___x_1833_ == 0)
{
v___y_1815_ = v_fileName_1824_;
v___y_1816_ = v_ref_1827_;
v___y_1817_ = v___f_1831_;
v___y_1818_ = v_fileMap_1825_;
v___y_1819_ = v_suppressElabErrors_1828_;
v___y_1820_ = v___y_1823_;
v___y_1821_ = v___x_1833_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = l_Lean_warningAsError;
v___x_1835_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSyntax_spec__1(v_options_1826_, v___x_1834_);
v___y_1815_ = v_fileName_1824_;
v___y_1816_ = v_ref_1827_;
v___y_1817_ = v___f_1831_;
v___y_1818_ = v_fileMap_1825_;
v___y_1819_ = v_suppressElabErrors_1828_;
v___y_1820_ = v___y_1823_;
v___y_1821_ = v___x_1835_;
goto v___jp_1814_;
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v_msgData_1721_);
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1840_, lean_object* v_msgData_1841_, lean_object* v_severity_1842_, lean_object* v_isSilent_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v_severity_boxed_1849_; uint8_t v_isSilent_boxed_1850_; lean_object* v_res_1851_; 
v_severity_boxed_1849_ = lean_unbox(v_severity_1842_);
v_isSilent_boxed_1850_ = lean_unbox(v_isSilent_1843_);
v_res_1851_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1840_, v_msgData_1841_, v_severity_boxed_1849_, v_isSilent_boxed_1850_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_ref_1840_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(lean_object* v_msgData_1852_, uint8_t v_severity_1853_, uint8_t v_isSilent_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_ref_1864_; lean_object* v___x_1865_; 
v_ref_1864_ = lean_ctor_get(v___y_1861_, 5);
v___x_1865_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1864_, v_msgData_1852_, v_severity_1853_, v_isSilent_1854_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0___boxed(lean_object* v_msgData_1866_, lean_object* v_severity_1867_, lean_object* v_isSilent_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v_severity_boxed_1878_; uint8_t v_isSilent_boxed_1879_; lean_object* v_res_1880_; 
v_severity_boxed_1878_ = lean_unbox(v_severity_1867_);
v_isSilent_boxed_1879_ = lean_unbox(v_isSilent_1868_);
v_res_1880_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1866_, v_severity_boxed_1878_, v_isSilent_boxed_1879_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object* v_msgData_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
uint8_t v___x_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = 0;
v___x_1892_ = 0;
v___x_1893_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0(v_msgData_1881_, v___x_1891_, v___x_1892_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object* v_msgData_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_msgData_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* v_ref_1906_, lean_object* v_e_1907_, lean_object* v_origSpan_x3f_1908_, uint8_t v_addSubgoalsMsg_1909_, lean_object* v_codeActionPrefix_x3f_1910_, lean_object* v_checkState_x3f_1911_, uint8_t v_tacticErrorAsInfo_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_1909_, v_checkState_x3f_1911_, v_e_1907_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
if (lean_obj_tag(v_a_1923_) == 0)
{
lean_object* v_val_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_val_1924_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v_a_1923_, 1);
v___x_1925_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_1926_ = 4;
v___x_1927_ = l_Lean_MessageData_nil;
v___x_1928_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_1906_, v_val_1924_, v_origSpan_x3f_1908_, v___x_1925_, v_codeActionPrefix_x3f_1910_, v___x_1926_, v___x_1927_, v_a_1919_, v_a_1920_);
return v___x_1928_;
}
else
{
lean_dec(v_codeActionPrefix_x3f_1910_);
lean_dec(v_origSpan_x3f_1908_);
lean_dec(v_ref_1906_);
if (v_tacticErrorAsInfo_1912_ == 0)
{
lean_object* v_val_1929_; lean_object* v___x_1930_; 
v_val_1929_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v_a_1923_, 1);
v___x_1930_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_1929_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
return v___x_1930_;
}
else
{
lean_object* v_val_1931_; lean_object* v___x_1932_; 
v_val_1931_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v_a_1923_, 1);
v___x_1932_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_val_1931_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
return v___x_1932_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_codeActionPrefix_x3f_1910_);
lean_dec(v_origSpan_x3f_1908_);
lean_dec(v_ref_1906_);
v_a_1933_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1922_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1922_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* v_ref_1941_, lean_object* v_e_1942_, lean_object* v_origSpan_x3f_1943_, lean_object* v_addSubgoalsMsg_1944_, lean_object* v_codeActionPrefix_x3f_1945_, lean_object* v_checkState_x3f_1946_, lean_object* v_tacticErrorAsInfo_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_1957_; uint8_t v_tacticErrorAsInfo_boxed_1958_; lean_object* v_res_1959_; 
v_addSubgoalsMsg_boxed_1957_ = lean_unbox(v_addSubgoalsMsg_1944_);
v_tacticErrorAsInfo_boxed_1958_ = lean_unbox(v_tacticErrorAsInfo_1947_);
v_res_1959_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(v_ref_1941_, v_e_1942_, v_origSpan_x3f_1943_, v_addSubgoalsMsg_boxed_1957_, v_codeActionPrefix_x3f_1945_, v_checkState_x3f_1946_, v_tacticErrorAsInfo_boxed_1958_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(lean_object* v_ref_1960_, lean_object* v_msgData_1961_, uint8_t v_severity_1962_, uint8_t v_isSilent_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___redArg(v_ref_1960_, v_msgData_1961_, v_severity_1962_, v_isSilent_1963_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1974_, lean_object* v_msgData_1975_, lean_object* v_severity_1976_, lean_object* v_isSilent_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v_severity_boxed_1987_; uint8_t v_isSilent_boxed_1988_; lean_object* v_res_1989_; 
v_severity_boxed_1987_ = lean_unbox(v_severity_1976_);
v_isSilent_boxed_1988_ = lean_unbox(v_isSilent_1977_);
v_res_1989_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0_spec__0_spec__1(v_ref_1974_, v_msgData_1975_, v_severity_boxed_1987_, v_isSilent_boxed_1988_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v_ref_1974_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(uint8_t v_tacticErrorAsInfo_1990_, lean_object* v_as_1991_, size_t v_sz_1992_, size_t v_i_1993_, lean_object* v_b_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_a_2001_; uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_1993_, v_sz_1992_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1994_);
return v___x_2006_;
}
else
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2033_; 
v_fst_2007_ = lean_ctor_get(v_b_1994_, 0);
v_snd_2008_ = lean_ctor_get(v_b_1994_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_b_1994_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2010_ = v_b_1994_;
v_isShared_2011_ = v_isSharedCheck_2033_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_b_1994_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2033_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_a_2012_; 
v_a_2012_ = lean_array_uget_borrowed(v_as_1991_, v_i_1993_);
if (lean_obj_tag(v_a_2012_) == 0)
{
lean_object* v_val_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v_val_2013_ = lean_ctor_get(v_a_2012_, 0);
lean_inc(v_val_2013_);
v___x_2014_ = lean_array_push(v_fst_2007_, v_val_2013_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_snd_2008_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
v_a_2001_ = v___x_2016_;
goto v___jp_2000_;
}
}
else
{
lean_object* v_val_2018_; 
v_val_2018_ = lean_ctor_get(v_a_2012_, 0);
if (v_tacticErrorAsInfo_1990_ == 0)
{
lean_object* v___x_2024_; 
lean_inc(v_val_2018_);
v___x_2024_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState_spec__2___redArg(v_val_2018_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_dec_ref_known(v___x_2024_, 1);
goto v___jp_2019_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
goto v___jp_2019_;
}
v___jp_2019_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_inc(v_val_2018_);
v___x_2020_ = lean_array_push(v_snd_2008_, v_val_2018_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2020_);
v___x_2022_ = v___x_2010_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_fst_2007_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
v_a_2001_ = v___x_2022_;
goto v___jp_2000_;
}
}
}
}
}
v___jp_2000_:
{
size_t v___x_2002_; size_t v___x_2003_; 
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1993_, v___x_2002_);
v_i_1993_ = v___x_2003_;
v_b_1994_ = v_a_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg___boxed(lean_object* v_tacticErrorAsInfo_2034_, lean_object* v_as_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2044_; size_t v_sz_boxed_2045_; size_t v_i_boxed_2046_; lean_object* v_res_2047_; 
v_tacticErrorAsInfo_boxed_2044_ = lean_unbox(v_tacticErrorAsInfo_2034_);
v_sz_boxed_2045_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2046_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_boxed_2044_, v_as_2035_, v_sz_boxed_2045_, v_i_boxed_2046_, v_b_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v_as_2035_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t v_addSubgoalsMsg_2048_, lean_object* v_checkState_x3f_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_bs_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
lean_dec(v_checkState_x3f_2049_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_bs_2052_);
return v___x_2063_;
}
else
{
lean_object* v_v_2064_; lean_object* v___x_2065_; 
v_v_2064_ = lean_array_uget_borrowed(v_bs_2052_, v_i_2051_);
lean_inc(v_v_2064_);
lean_inc(v_checkState_x3f_2049_);
v___x_2065_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(v_addSubgoalsMsg_2048_, v_checkState_x3f_2049_, v_v_2064_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v_bs_x27_2068_; size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = lean_unsigned_to_nat(0u);
v_bs_x27_2068_ = lean_array_uset(v_bs_2052_, v_i_2051_, v___x_2067_);
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_add(v_i_2051_, v___x_2069_);
v___x_2071_ = lean_array_uset(v_bs_x27_2068_, v_i_2051_, v_a_2066_);
v_i_2051_ = v___x_2070_;
v_bs_2052_ = v___x_2071_;
goto _start;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_bs_2052_);
lean_dec(v_checkState_x3f_2049_);
v_a_2073_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2065_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2065_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object* v_addSubgoalsMsg_2081_, lean_object* v_checkState_x3f_2082_, lean_object* v_sz_2083_, lean_object* v_i_2084_, lean_object* v_bs_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2095_; size_t v_sz_boxed_2096_; size_t v_i_boxed_2097_; lean_object* v_res_2098_; 
v_addSubgoalsMsg_boxed_2095_ = lean_unbox(v_addSubgoalsMsg_2081_);
v_sz_boxed_2096_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2097_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_boxed_2095_, v_checkState_x3f_2082_, v_sz_boxed_2096_, v_i_boxed_2097_, v_bs_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(lean_object* v_as_2099_, size_t v_sz_2100_, size_t v_i_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_usize_dec_lt(v_i_2101_, v_sz_2100_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v_b_2102_);
return v___x_2113_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_array_uget_borrowed(v_as_2099_, v_i_2101_);
lean_inc(v_a_2114_);
v___x_2115_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v_a_2114_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; 
lean_dec_ref_known(v___x_2115_, 1);
v___x_2116_ = lean_box(0);
v___x_2117_ = ((size_t)1ULL);
v___x_2118_ = lean_usize_add(v_i_2101_, v___x_2117_);
v_i_2101_ = v___x_2118_;
v_b_2102_ = v___x_2116_;
goto _start;
}
else
{
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2___boxed(lean_object* v_as_2120_, lean_object* v_sz_2121_, lean_object* v_i_2122_, lean_object* v_b_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
size_t v_sz_boxed_2133_; size_t v_i_boxed_2134_; lean_object* v_res_2135_; 
v_sz_boxed_2133_ = lean_unbox_usize(v_sz_2121_);
lean_dec(v_sz_2121_);
v_i_boxed_2134_ = lean_unbox_usize(v_i_2122_);
lean_dec(v_i_2122_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_as_2120_, v_sz_boxed_2133_, v_i_boxed_2134_, v_b_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v_as_2120_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* v_ref_2141_, lean_object* v_es_2142_, lean_object* v_origSpan_x3f_2143_, uint8_t v_addSubgoalsMsg_2144_, lean_object* v_codeActionPrefix_x3f_2145_, lean_object* v_checkState_x3f_2146_, uint8_t v_tacticErrorAsInfo_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v_sz_2157_ = lean_array_size(v_es_2142_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(v_addSubgoalsMsg_2144_, v_checkState_x3f_2146_, v_sz_2157_, v___x_2158_, v_es_2142_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; size_t v_sz_2162_; lean_object* v___x_2163_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1));
v_sz_2162_ = lean_array_size(v_a_2160_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2147_, v_a_2160_, v_sz_2162_, v___x_2158_, v___x_2161_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2160_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_fst_2165_; lean_object* v_snd_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_fst_2165_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_fst_2165_);
v_snd_2166_ = lean_ctor_get(v_a_2164_, 1);
lean_inc(v_snd_2166_);
lean_dec(v_a_2164_);
v___x_2167_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2));
v___x_2168_ = 4;
v___x_2169_ = l_Lean_MessageData_nil;
v___x_2170_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2141_, v_fst_2165_, v_origSpan_x3f_2143_, v___x_2167_, v_codeActionPrefix_x3f_2145_, v___x_2168_, v___x_2169_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; size_t v_sz_2172_; lean_object* v___x_2173_; 
lean_dec_ref_known(v___x_2170_, 1);
v___x_2171_ = lean_box(0);
v_sz_2172_ = lean_array_size(v_snd_2166_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__2(v_snd_2166_, v_sz_2172_, v___x_2158_, v___x_2171_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_snd_2166_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2173_, 0);
lean_dec(v_unused_2181_);
v___x_2175_ = v___x_2173_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_dec(v___x_2173_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2171_);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2171_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
else
{
return v___x_2173_;
}
}
else
{
lean_dec(v_snd_2166_);
return v___x_2170_;
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_codeActionPrefix_x3f_2145_);
lean_dec(v_origSpan_x3f_2143_);
lean_dec(v_ref_2141_);
v_a_2182_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2163_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2163_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_codeActionPrefix_x3f_2145_);
lean_dec(v_origSpan_x3f_2143_);
lean_dec(v_ref_2141_);
v_a_2190_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2159_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2159_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* v_ref_2198_, lean_object* v_es_2199_, lean_object* v_origSpan_x3f_2200_, lean_object* v_addSubgoalsMsg_2201_, lean_object* v_codeActionPrefix_x3f_2202_, lean_object* v_checkState_x3f_2203_, lean_object* v_tacticErrorAsInfo_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
uint8_t v_addSubgoalsMsg_boxed_2214_; uint8_t v_tacticErrorAsInfo_boxed_2215_; lean_object* v_res_2216_; 
v_addSubgoalsMsg_boxed_2214_ = lean_unbox(v_addSubgoalsMsg_2201_);
v_tacticErrorAsInfo_boxed_2215_ = lean_unbox(v_tacticErrorAsInfo_2204_);
v_res_2216_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(v_ref_2198_, v_es_2199_, v_origSpan_x3f_2200_, v_addSubgoalsMsg_boxed_2214_, v_codeActionPrefix_x3f_2202_, v_checkState_x3f_2203_, v_tacticErrorAsInfo_boxed_2215_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t v_tacticErrorAsInfo_2217_, lean_object* v_as_2218_, size_t v_sz_2219_, size_t v_i_2220_, lean_object* v_b_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___redArg(v_tacticErrorAsInfo_2217_, v_as_2218_, v_sz_2219_, v_i_2220_, v_b_2221_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object* v_tacticErrorAsInfo_2232_, lean_object* v_as_2233_, lean_object* v_sz_2234_, lean_object* v_i_2235_, lean_object* v_b_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
uint8_t v_tacticErrorAsInfo_boxed_2246_; size_t v_sz_boxed_2247_; size_t v_i_boxed_2248_; lean_object* v_res_2249_; 
v_tacticErrorAsInfo_boxed_2246_ = lean_unbox(v_tacticErrorAsInfo_2232_);
v_sz_boxed_2247_ = lean_unbox_usize(v_sz_2234_);
lean_dec(v_sz_2234_);
v_i_boxed_2248_ = lean_unbox_usize(v_i_2235_);
lean_dec(v_i_2235_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(v_tacticErrorAsInfo_boxed_2246_, v_as_2233_, v_sz_boxed_2247_, v_i_boxed_2248_, v_b_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_as_2233_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* v_ref_2250_, lean_object* v_e_2251_, lean_object* v_origSpan_x3f_2252_, lean_object* v_header_2253_, lean_object* v_codeActionPrefix_x3f_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_e_2251_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = 4;
v___x_2263_ = l_Lean_MessageData_nil;
v___x_2264_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2250_, v_a_2261_, v_origSpan_x3f_2252_, v_header_2253_, v_codeActionPrefix_x3f_2254_, v___x_2262_, v___x_2263_, v_a_2257_, v_a_2258_);
return v___x_2264_;
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_codeActionPrefix_x3f_2254_);
lean_dec_ref(v_header_2253_);
lean_dec(v_origSpan_x3f_2252_);
lean_dec(v_ref_2250_);
v_a_2265_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2260_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2260_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object* v_ref_2273_, lean_object* v_e_2274_, lean_object* v_origSpan_x3f_2275_, lean_object* v_header_2276_, lean_object* v_codeActionPrefix_x3f_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(v_ref_2273_, v_e_2274_, v_origSpan_x3f_2275_, v_header_2276_, v_codeActionPrefix_x3f_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t v_sz_2284_, size_t v_i_2285_, lean_object* v_bs_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v___x_2292_; 
v___x_2292_ = lean_usize_dec_lt(v_i_2285_, v_sz_2284_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_bs_2286_);
return v___x_2293_;
}
else
{
lean_object* v_v_2294_; lean_object* v___x_2295_; 
v_v_2294_ = lean_array_uget_borrowed(v_bs_2286_, v_i_2285_);
lean_inc(v_v_2294_);
v___x_2295_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(v_v_2294_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v_bs_x27_2298_; size_t v___x_2299_; size_t v___x_2300_; lean_object* v___x_2301_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = lean_unsigned_to_nat(0u);
v_bs_x27_2298_ = lean_array_uset(v_bs_2286_, v_i_2285_, v___x_2297_);
v___x_2299_ = ((size_t)1ULL);
v___x_2300_ = lean_usize_add(v_i_2285_, v___x_2299_);
v___x_2301_ = lean_array_uset(v_bs_x27_2298_, v_i_2285_, v_a_2296_);
v_i_2285_ = v___x_2300_;
v_bs_2286_ = v___x_2301_;
goto _start;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_bs_2286_);
v_a_2303_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2295_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2295_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object* v_sz_2311_, lean_object* v_i_2312_, lean_object* v_bs_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
size_t v_sz_boxed_2319_; size_t v_i_boxed_2320_; lean_object* v_res_2321_; 
v_sz_boxed_2319_ = lean_unbox_usize(v_sz_2311_);
lean_dec(v_sz_2311_);
v_i_boxed_2320_ = lean_unbox_usize(v_i_2312_);
lean_dec(v_i_2312_);
v_res_2321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_boxed_2319_, v_i_boxed_2320_, v_bs_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* v_ref_2322_, lean_object* v_es_2323_, lean_object* v_origSpan_x3f_2324_, lean_object* v_header_2325_, lean_object* v_codeActionPrefix_x3f_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
size_t v_sz_2332_; size_t v___x_2333_; lean_object* v___x_2334_; 
v_sz_2332_ = lean_array_size(v_es_2323_);
v___x_2333_ = ((size_t)0ULL);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(v_sz_2332_, v___x_2333_, v_es_2323_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = 4;
v___x_2337_ = l_Lean_MessageData_nil;
v___x_2338_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_2322_, v_a_2335_, v_origSpan_x3f_2324_, v_header_2325_, v_codeActionPrefix_x3f_2326_, v___x_2336_, v___x_2337_, v_a_2329_, v_a_2330_);
return v___x_2338_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_codeActionPrefix_x3f_2326_);
lean_dec_ref(v_header_2325_);
lean_dec(v_origSpan_x3f_2324_);
lean_dec(v_ref_2322_);
v_a_2339_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2334_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2334_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object* v_ref_2347_, lean_object* v_es_2348_, lean_object* v_origSpan_x3f_2349_, lean_object* v_header_2350_, lean_object* v_codeActionPrefix_x3f_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(v_ref_2347_, v_es_2348_, v_origSpan_x3f_2349_, v_header_2350_, v_codeActionPrefix_x3f_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
return v_res_2357_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Array_mkArray0(lean_box(0));
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__14));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__16));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__21));
v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_2422_ = l_String_toRawSubstring_x27(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__80));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__82));
v___x_2564_ = l_Lean_stringToMessageData(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__84));
v___x_2567_ = l_Lean_stringToMessageData(v___x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object* v_e_2568_, lean_object* v_t_x3f_2569_, uint8_t v_a_2570_, lean_object* v_h_x3f_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___x_2594_; 
lean_inc_ref(v_e_2568_);
v___x_2594_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_e_2568_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___y_2597_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
if (lean_obj_tag(v_t_x3f_2569_) == 1)
{
lean_object* v_val_2625_; lean_object* v___x_2626_; 
v_val_2625_ = lean_ctor_get(v_t_x3f_2569_, 0);
lean_inc_n(v_val_2625_, 2);
lean_dec_ref_known(v_t_x3f_2569_, 1);
v___x_2626_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_val_2625_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___y_2629_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
if (v_a_2570_ == 0)
{
if (lean_obj_tag(v_h_x3f_2571_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2629_ = v___x_2666_;
goto v___jp_2628_;
}
else
{
lean_object* v_val_2667_; 
v_val_2667_ = lean_ctor_get(v_h_x3f_2571_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_h_x3f_2571_, 1);
v___y_2629_ = v_val_2667_;
goto v___jp_2628_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2571_) == 0)
{
lean_object* v_ref_2668_; lean_object* v_quotContext_2669_; lean_object* v_currMacroScope_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_ref_2668_ = lean_ctor_get(v___y_2574_, 5);
v_quotContext_2669_ = lean_ctor_get(v___y_2574_, 10);
v_currMacroScope_2670_ = lean_ctor_get(v___y_2574_, 11);
v___x_2671_ = 0;
v___x_2672_ = l_Lean_SourceInfo_fromRef(v_ref_2668_, v___x_2671_);
v___x_2673_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2674_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2672_, 12);
v___x_2675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2672_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2678_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2672_);
lean_ctor_set(v___x_2679_, 1, v___x_2677_);
lean_ctor_set(v___x_2679_, 2, v___x_2678_);
lean_inc_ref(v___x_2679_);
v___x_2680_ = l_Lean_Syntax_node1(v___x_2672_, v___x_2676_, v___x_2679_);
v___x_2681_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2682_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2683_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2684_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2685_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2686_ = lean_box(0);
lean_inc(v_currMacroScope_2670_);
lean_inc(v_quotContext_2669_);
v___x_2687_ = l_Lean_addMacroScope(v_quotContext_2669_, v___x_2686_, v_currMacroScope_2670_);
v___x_2688_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2689_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2672_);
lean_ctor_set(v___x_2689_, 1, v___x_2685_);
lean_ctor_set(v___x_2689_, 2, v___x_2687_);
lean_ctor_set(v___x_2689_, 3, v___x_2688_);
v___x_2690_ = l_Lean_Syntax_node1(v___x_2672_, v___x_2684_, v___x_2689_);
v___x_2691_ = l_Lean_Syntax_node1(v___x_2672_, v___x_2683_, v___x_2690_);
v___x_2692_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2693_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2672_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l_Lean_Syntax_node2(v___x_2672_, v___x_2692_, v___x_2694_, v_a_2627_);
v___x_2696_ = l_Lean_Syntax_node1(v___x_2672_, v___x_2677_, v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2672_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Lean_Syntax_node5(v___x_2672_, v___x_2682_, v___x_2691_, v___x_2679_, v___x_2696_, v___x_2698_, v_a_2595_);
v___x_2700_ = l_Lean_Syntax_node1(v___x_2672_, v___x_2681_, v___x_2699_);
v___x_2701_ = l_Lean_Syntax_node3(v___x_2672_, v___x_2673_, v___x_2675_, v___x_2680_, v___x_2700_);
v___x_2702_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__81);
v___x_2703_ = l_Lean_MessageData_ofExpr(v_val_2625_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = l_Lean_MessageData_ofExpr(v_e_2568_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v_fst_2578_ = v___x_2701_;
v_snd_2579_ = v___x_2708_;
v___y_2580_ = v___y_2572_;
v___y_2581_ = v___y_2573_;
v___y_2582_ = v___y_2574_;
v___y_2583_ = v___y_2575_;
goto v___jp_2577_;
}
else
{
lean_object* v_val_2709_; lean_object* v_ref_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_val_2709_ = lean_ctor_get(v_h_x3f_2571_, 0);
lean_inc_n(v_val_2709_, 2);
lean_dec_ref_known(v_h_x3f_2571_, 1);
v_ref_2710_ = lean_ctor_get(v___y_2574_, 5);
v___x_2711_ = 0;
v___x_2712_ = l_Lean_SourceInfo_fromRef(v_ref_2710_, v___x_2711_);
v___x_2713_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2714_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2712_, 10);
v___x_2715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2718_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2712_);
lean_ctor_set(v___x_2719_, 1, v___x_2717_);
lean_ctor_set(v___x_2719_, 2, v___x_2718_);
lean_inc_ref(v___x_2719_);
v___x_2720_ = l_Lean_Syntax_node1(v___x_2712_, v___x_2716_, v___x_2719_);
v___x_2721_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2722_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2723_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2724_ = lean_mk_syntax_ident(v_val_2709_);
v___x_2725_ = l_Lean_Syntax_node1(v___x_2712_, v___x_2723_, v___x_2724_);
v___x_2726_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2727_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2712_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = l_Lean_Syntax_node2(v___x_2712_, v___x_2726_, v___x_2728_, v_a_2627_);
v___x_2730_ = l_Lean_Syntax_node1(v___x_2712_, v___x_2717_, v___x_2729_);
v___x_2731_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2712_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = l_Lean_Syntax_node5(v___x_2712_, v___x_2722_, v___x_2725_, v___x_2719_, v___x_2730_, v___x_2732_, v_a_2595_);
v___x_2734_ = l_Lean_Syntax_node1(v___x_2712_, v___x_2721_, v___x_2733_);
v___x_2735_ = l_Lean_Syntax_node3(v___x_2712_, v___x_2713_, v___x_2715_, v___x_2720_, v___x_2734_);
v___x_2736_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2737_ = l_Lean_MessageData_ofName(v_val_2709_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofExpr(v_val_2625_);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = l_Lean_MessageData_ofExpr(v_e_2568_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v_fst_2578_ = v___x_2735_;
v_snd_2579_ = v___x_2746_;
v___y_2580_ = v___y_2572_;
v___y_2581_ = v___y_2573_;
v___y_2582_ = v___y_2574_;
v___y_2583_ = v___y_2575_;
goto v___jp_2577_;
}
}
v___jp_2628_:
{
lean_object* v_ref_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_ref_2630_ = lean_ctor_get(v___y_2574_, 5);
v___x_2631_ = l_Lean_SourceInfo_fromRef(v_ref_2630_, v_a_2570_);
v___x_2632_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2633_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2631_, 10);
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2631_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2637_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2631_);
lean_ctor_set(v___x_2638_, 1, v___x_2636_);
lean_ctor_set(v___x_2638_, 2, v___x_2637_);
lean_inc_ref(v___x_2638_);
v___x_2639_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2635_, v___x_2638_);
v___x_2640_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2641_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2642_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2629_);
v___x_2643_ = lean_mk_syntax_ident(v___y_2629_);
v___x_2644_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2642_, v___x_2643_);
v___x_2645_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__19));
v___x_2646_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__20));
v___x_2647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2631_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_Syntax_node2(v___x_2631_, v___x_2645_, v___x_2647_, v_a_2627_);
v___x_2649_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2636_, v___x_2648_);
v___x_2650_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2631_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_Syntax_node5(v___x_2631_, v___x_2641_, v___x_2644_, v___x_2638_, v___x_2649_, v___x_2651_, v_a_2595_);
v___x_2653_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2640_, v___x_2652_);
v___x_2654_ = l_Lean_Syntax_node3(v___x_2631_, v___x_2632_, v___x_2634_, v___x_2639_, v___x_2653_);
v___x_2655_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2656_ = l_Lean_MessageData_ofName(v___y_2629_);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__22);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = l_Lean_MessageData_ofExpr(v_val_2625_);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = l_Lean_MessageData_ofExpr(v_e_2568_);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v_fst_2578_ = v___x_2654_;
v_snd_2579_ = v___x_2665_;
v___y_2580_ = v___y_2572_;
v___y_2581_ = v___y_2573_;
v___y_2582_ = v___y_2574_;
v___y_2583_ = v___y_2575_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_val_2625_);
lean_dec(v_a_2595_);
lean_dec_ref(v___y_2574_);
lean_dec(v_h_x3f_2571_);
lean_dec_ref(v_e_2568_);
v_a_2747_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2626_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2626_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_dec(v_t_x3f_2569_);
if (v_a_2570_ == 0)
{
if (lean_obj_tag(v_h_x3f_2571_) == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__24));
v___y_2597_ = v___x_2755_;
goto v___jp_2596_;
}
else
{
lean_object* v_val_2756_; 
v_val_2756_ = lean_ctor_get(v_h_x3f_2571_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v_h_x3f_2571_, 1);
v___y_2597_ = v_val_2756_;
goto v___jp_2596_;
}
}
else
{
if (lean_obj_tag(v_h_x3f_2571_) == 0)
{
lean_object* v_ref_2757_; lean_object* v_quotContext_2758_; lean_object* v_currMacroScope_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_ref_2757_ = lean_ctor_get(v___y_2574_, 5);
v_quotContext_2758_ = lean_ctor_get(v___y_2574_, 10);
v_currMacroScope_2759_ = lean_ctor_get(v___y_2574_, 11);
v___x_2760_ = 0;
v___x_2761_ = l_Lean_SourceInfo_fromRef(v_ref_2757_, v___x_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2763_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2761_, 9);
v___x_2764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2761_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2767_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2761_);
lean_ctor_set(v___x_2768_, 1, v___x_2766_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
lean_inc_ref_n(v___x_2768_, 2);
v___x_2769_ = l_Lean_Syntax_node1(v___x_2761_, v___x_2765_, v___x_2768_);
v___x_2770_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2771_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2772_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2773_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__29));
v___x_2774_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__30);
v___x_2775_ = lean_box(0);
lean_inc(v_currMacroScope_2759_);
lean_inc(v_quotContext_2758_);
v___x_2776_ = l_Lean_addMacroScope(v_quotContext_2758_, v___x_2775_, v_currMacroScope_2759_);
v___x_2777_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__79));
v___x_2778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2761_);
lean_ctor_set(v___x_2778_, 1, v___x_2774_);
lean_ctor_set(v___x_2778_, 2, v___x_2776_);
lean_ctor_set(v___x_2778_, 3, v___x_2777_);
v___x_2779_ = l_Lean_Syntax_node1(v___x_2761_, v___x_2773_, v___x_2778_);
v___x_2780_ = l_Lean_Syntax_node1(v___x_2761_, v___x_2772_, v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2761_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_Syntax_node5(v___x_2761_, v___x_2771_, v___x_2780_, v___x_2768_, v___x_2768_, v___x_2782_, v_a_2595_);
v___x_2784_ = l_Lean_Syntax_node1(v___x_2761_, v___x_2770_, v___x_2783_);
v___x_2785_ = l_Lean_Syntax_node3(v___x_2761_, v___x_2762_, v___x_2764_, v___x_2769_, v___x_2784_);
v___x_2786_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__85);
v___x_2787_ = l_Lean_MessageData_ofExpr(v_e_2568_);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v_fst_2578_ = v___x_2785_;
v_snd_2579_ = v___x_2788_;
v___y_2580_ = v___y_2572_;
v___y_2581_ = v___y_2573_;
v___y_2582_ = v___y_2574_;
v___y_2583_ = v___y_2575_;
goto v___jp_2577_;
}
else
{
lean_object* v_val_2789_; lean_object* v_ref_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_val_2789_ = lean_ctor_get(v_h_x3f_2571_, 0);
lean_inc_n(v_val_2789_, 2);
lean_dec_ref_known(v_h_x3f_2571_, 1);
v_ref_2790_ = lean_ctor_get(v___y_2574_, 5);
v___x_2791_ = 0;
v___x_2792_ = l_Lean_SourceInfo_fromRef(v_ref_2790_, v___x_2791_);
v___x_2793_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__26));
v___x_2794_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__27));
lean_inc_n(v___x_2792_, 7);
v___x_2795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2792_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2798_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2792_);
lean_ctor_set(v___x_2799_, 1, v___x_2797_);
lean_ctor_set(v___x_2799_, 2, v___x_2798_);
lean_inc_ref_n(v___x_2799_, 2);
v___x_2800_ = l_Lean_Syntax_node1(v___x_2792_, v___x_2796_, v___x_2799_);
v___x_2801_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2802_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2803_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
v___x_2804_ = lean_mk_syntax_ident(v_val_2789_);
v___x_2805_ = l_Lean_Syntax_node1(v___x_2792_, v___x_2803_, v___x_2804_);
v___x_2806_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2792_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = l_Lean_Syntax_node5(v___x_2792_, v___x_2802_, v___x_2805_, v___x_2799_, v___x_2799_, v___x_2807_, v_a_2595_);
v___x_2809_ = l_Lean_Syntax_node1(v___x_2792_, v___x_2801_, v___x_2808_);
v___x_2810_ = l_Lean_Syntax_node3(v___x_2792_, v___x_2793_, v___x_2795_, v___x_2800_, v___x_2809_);
v___x_2811_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__83);
v___x_2812_ = l_Lean_MessageData_ofName(v_val_2789_);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l_Lean_MessageData_ofExpr(v_e_2568_);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v_fst_2578_ = v___x_2810_;
v_snd_2579_ = v___x_2817_;
v___y_2580_ = v___y_2572_;
v___y_2581_ = v___y_2573_;
v___y_2582_ = v___y_2574_;
v___y_2583_ = v___y_2575_;
goto v___jp_2577_;
}
}
}
v___jp_2596_:
{
lean_object* v_ref_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_ref_2598_ = lean_ctor_get(v___y_2574_, 5);
v___x_2599_ = l_Lean_SourceInfo_fromRef(v_ref_2598_, v_a_2570_);
v___x_2600_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__1));
v___x_2601_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__2));
lean_inc_n(v___x_2599_, 7);
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__5));
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_2605_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_2606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2599_);
lean_ctor_set(v___x_2606_, 1, v___x_2604_);
lean_ctor_set(v___x_2606_, 2, v___x_2605_);
lean_inc_ref_n(v___x_2606_, 2);
v___x_2607_ = l_Lean_Syntax_node1(v___x_2599_, v___x_2603_, v___x_2606_);
v___x_2608_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__8));
v___x_2609_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__10));
v___x_2610_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__12));
lean_inc(v___y_2597_);
v___x_2611_ = lean_mk_syntax_ident(v___y_2597_);
v___x_2612_ = l_Lean_Syntax_node1(v___x_2599_, v___x_2610_, v___x_2611_);
v___x_2613_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__13));
v___x_2614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2599_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = l_Lean_Syntax_node5(v___x_2599_, v___x_2609_, v___x_2612_, v___x_2606_, v___x_2606_, v___x_2614_, v_a_2595_);
v___x_2616_ = l_Lean_Syntax_node1(v___x_2599_, v___x_2608_, v___x_2615_);
v___x_2617_ = l_Lean_Syntax_node3(v___x_2599_, v___x_2600_, v___x_2602_, v___x_2607_, v___x_2616_);
v___x_2618_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__15);
v___x_2619_ = l_Lean_MessageData_ofName(v___y_2597_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__17);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = l_Lean_MessageData_ofExpr(v_e_2568_);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v_fst_2578_ = v___x_2617_;
v_snd_2579_ = v___x_2624_;
v___y_2580_ = v___y_2572_;
v___y_2581_ = v___y_2573_;
v___y_2582_ = v___y_2574_;
v___y_2583_ = v___y_2575_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v___y_2574_);
lean_dec(v_h_x3f_2571_);
lean_dec(v_t_x3f_2569_);
lean_dec_ref(v_e_2568_);
v_a_2818_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2594_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2594_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
v___jp_2577_:
{
lean_object* v___x_2584_; lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v___x_2584_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v_snd_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec_ref(v___y_2582_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_fst_2578_);
lean_ctor_set(v___x_2589_, 1, v_a_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object* v_e_2826_, lean_object* v_t_x3f_2827_, lean_object* v_a_2828_, lean_object* v_h_x3f_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
uint8_t v_a_17939__boxed_2835_; lean_object* v_res_2836_; 
v_a_17939__boxed_2835_ = lean_unbox(v_a_2828_);
v_res_2836_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(v_e_2826_, v_t_x3f_2827_, v_a_17939__boxed_2835_, v_h_x3f_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
return v_res_2836_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1));
v___x_2841_ = l_Lean_MessageData_ofFormat(v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* v_ref_2842_, lean_object* v_h_x3f_2843_, lean_object* v_t_x3f_2844_, lean_object* v_e_2845_, lean_object* v_origSpan_x3f_2846_, lean_object* v_checkState_x3f_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_tac_2858_; lean_object* v_msg_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___x_2871_; 
lean_inc(v_a_2855_);
lean_inc_ref(v_a_2854_);
lean_inc(v_a_2853_);
lean_inc_ref(v_a_2852_);
lean_inc_ref(v_e_2845_);
v___x_2871_ = lean_infer_type(v_e_2845_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_Meta_isProp(v_a_2872_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___f_2875_; lean_object* v___x_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___f_2875_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2875_, 0, v_e_2845_);
lean_closure_set(v___f_2875_, 1, v_t_x3f_2844_);
lean_closure_set(v___f_2875_, 2, v_a_2874_);
lean_closure_set(v___f_2875_, 3, v_h_x3f_2843_);
v___x_2876_ = l_Lean_Meta_withExposedNames___redArg(v___f_2875_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
if (lean_obj_tag(v_checkState_x3f_2847_) == 1)
{
lean_object* v_fst_2878_; lean_object* v_snd_2879_; lean_object* v_val_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_fst_2878_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_fst_2878_);
v_snd_2879_ = lean_ctor_get(v_a_2877_, 1);
lean_inc_n(v_snd_2879_, 2);
lean_dec(v_a_2877_);
v_val_2880_ = lean_ctor_get(v_checkState_x3f_2847_, 0);
lean_inc(v_val_2880_);
lean_dec_ref_known(v_checkState_x3f_2847_, 1);
v___x_2881_ = lean_box(0);
v___x_2882_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_2878_, v_snd_2879_, v_val_2880_, v___x_2881_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
if (lean_obj_tag(v_a_2883_) == 1)
{
lean_object* v_val_2884_; lean_object* v_fst_2885_; lean_object* v_snd_2886_; 
lean_dec(v_snd_2879_);
v_val_2884_ = lean_ctor_get(v_a_2883_, 0);
lean_inc(v_val_2884_);
lean_dec_ref_known(v_a_2883_, 1);
v_fst_2885_ = lean_ctor_get(v_val_2884_, 0);
lean_inc(v_fst_2885_);
v_snd_2886_ = lean_ctor_get(v_val_2884_, 1);
lean_inc(v_snd_2886_);
lean_dec(v_val_2884_);
v_tac_2858_ = v_fst_2885_;
v_msg_2859_ = v_snd_2886_;
v___y_2860_ = v_a_2854_;
v___y_2861_ = v_a_2855_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec(v_a_2883_);
lean_dec(v_origSpan_x3f_2846_);
lean_dec(v_ref_2842_);
v___x_2887_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
v___x_2888_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_2887_, v_snd_2879_);
v___x_2889_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_2888_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2897_; 
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2889_, 0);
lean_dec(v_unused_2898_);
v___x_2891_ = v___x_2889_;
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v___x_2889_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_box(0);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2895_ = v___x_2891_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
return v___x_2889_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_snd_2879_);
lean_dec(v_origSpan_x3f_2846_);
lean_dec(v_ref_2842_);
v_a_2899_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2882_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2882_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_fst_2907_; lean_object* v_snd_2908_; 
lean_dec(v_checkState_x3f_2847_);
v_fst_2907_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_fst_2907_);
v_snd_2908_ = lean_ctor_get(v_a_2877_, 1);
lean_inc(v_snd_2908_);
lean_dec(v_a_2877_);
v_tac_2858_ = v_fst_2907_;
v_msg_2859_ = v_snd_2908_;
v___y_2860_ = v_a_2854_;
v___y_2861_ = v_a_2855_;
goto v___jp_2857_;
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec(v_checkState_x3f_2847_);
lean_dec(v_origSpan_x3f_2846_);
lean_dec(v_ref_2842_);
v_a_2909_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2876_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2876_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_checkState_x3f_2847_);
lean_dec(v_origSpan_x3f_2846_);
lean_dec_ref(v_e_2845_);
lean_dec(v_t_x3f_2844_);
lean_dec(v_h_x3f_2843_);
lean_dec(v_ref_2842_);
v_a_2917_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2873_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2873_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_checkState_x3f_2847_);
lean_dec(v_origSpan_x3f_2846_);
lean_dec_ref(v_e_2845_);
lean_dec(v_t_x3f_2844_);
lean_dec(v_h_x3f_2843_);
lean_dec(v_ref_2842_);
v_a_2925_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2871_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2871_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
v___jp_2857_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v_tac_2858_);
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_msg_2859_);
v___x_2866_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2863_);
lean_ctor_set(v___x_2866_, 1, v___x_2864_);
lean_ctor_set(v___x_2866_, 2, v___x_2864_);
lean_ctor_set(v___x_2866_, 3, v___x_2864_);
lean_ctor_set(v___x_2866_, 4, v___x_2865_);
lean_ctor_set(v___x_2866_, 5, v___x_2864_);
v___x_2867_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_2868_ = 4;
v___x_2869_ = l_Lean_MessageData_nil;
v___x_2870_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_2842_, v___x_2866_, v_origSpan_x3f_2846_, v___x_2867_, v___x_2864_, v___x_2868_, v___x_2869_, v___y_2860_, v___y_2861_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object* v_ref_2933_, lean_object* v_h_x3f_2934_, lean_object* v_t_x3f_2935_, lean_object* v_e_2936_, lean_object* v_origSpan_x3f_2937_, lean_object* v_checkState_x3f_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(v_ref_2933_, v_h_x3f_2934_, v_t_x3f_2935_, v_e_2936_, v_origSpan_x3f_2937_, v_checkState_x3f_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
if (lean_obj_tag(v_a_2950_) == 0)
{
lean_object* v___x_2952_; 
v___x_2952_ = l_List_reverse___redArg(v_a_2951_);
return v___x_2952_;
}
else
{
lean_object* v_head_2953_; lean_object* v_tail_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2986_; 
v_head_2953_ = lean_ctor_get(v_a_2950_, 0);
v_tail_2954_ = lean_ctor_get(v_a_2950_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_a_2950_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2956_ = v_a_2950_;
v_isShared_2957_ = v_isSharedCheck_2986_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_tail_2954_);
lean_inc(v_head_2953_);
lean_dec(v_a_2950_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2986_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___y_2959_; lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2985_; 
v_fst_2964_ = lean_ctor_get(v_head_2953_, 0);
v_snd_2965_ = lean_ctor_get(v_head_2953_, 1);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_head_2953_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2967_ = v_head_2953_;
v_isShared_2968_ = v_isSharedCheck_2985_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_snd_2965_);
lean_inc(v_fst_2964_);
lean_dec(v_head_2953_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2985_;
goto v_resetjp_2966_;
}
v___jp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v_a_2951_);
lean_ctor_set(v___x_2956_, 0, v___y_2959_);
v___x_2961_ = v___x_2956_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___y_2959_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_a_2951_);
v___x_2961_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
v_a_2950_ = v_tail_2954_;
v_a_2951_ = v___x_2961_;
goto _start;
}
}
v_resetjp_2966_:
{
lean_object* v___y_2970_; uint8_t v___x_2982_; 
v___x_2982_ = lean_unbox(v_snd_2965_);
lean_dec(v_snd_2965_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___y_2970_ = v___x_2983_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1___closed__0));
v___y_2970_ = v___x_2984_;
goto v___jp_2969_;
}
v___jp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
lean_inc_ref(v___y_2970_);
v___x_2971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2970_);
v___x_2972_ = l_Lean_MessageData_ofFormat(v___x_2971_);
v___x_2973_ = l_Lean_Expr_isConst(v_fst_2964_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2974_ = l_Lean_MessageData_ofExpr(v_fst_2964_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 7);
lean_ctor_set(v___x_2967_, 1, v___x_2974_);
lean_ctor_set(v___x_2967_, 0, v___x_2972_);
v___x_2976_ = v___x_2967_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v___y_2959_ = v___x_2976_;
goto v___jp_2958_;
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = l_Lean_MessageData_ofConst(v_fst_2964_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 7);
lean_ctor_set(v___x_2967_, 1, v___x_2978_);
lean_ctor_set(v___x_2967_, 0, v___x_2972_);
v___x_2980_ = v___x_2967_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
v___y_2959_ = v___x_2980_;
goto v___jp_2958_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t v_sz_2994_, size_t v_i_2995_, lean_object* v_bs_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_lt(v_i_2995_, v_sz_2994_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_bs_2996_);
return v___x_3003_;
}
else
{
lean_object* v_v_3004_; lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3050_; 
v_v_3004_ = lean_array_uget(v_bs_2996_, v_i_2995_);
v_fst_3005_ = lean_ctor_get(v_v_3004_, 0);
v_snd_3006_ = lean_ctor_get(v_v_3004_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_v_3004_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3008_ = v_v_3004_;
v_isShared_3009_ = v_isSharedCheck_3050_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snd_3006_);
lean_inc(v_fst_3005_);
lean_dec(v_v_3004_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3050_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v_bs_x27_3011_; lean_object* v_a_3013_; lean_object* v___x_3018_; 
v___x_3010_ = lean_unsigned_to_nat(0u);
v_bs_x27_3011_ = lean_array_uset(v_bs_2996_, v_i_2995_, v___x_3010_);
v___x_3018_ = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(v_fst_3005_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3018_) == 0)
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_unbox(v_snd_3006_);
if (v___x_3019_ == 0)
{
lean_object* v_a_3020_; lean_object* v_ref_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_del_object(v___x_3008_);
v_a_3020_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3018_, 1);
v_ref_3021_ = lean_ctor_get(v___y_2999_, 5);
v___x_3022_ = lean_unbox(v_snd_3006_);
lean_dec(v_snd_3006_);
v___x_3023_ = l_Lean_SourceInfo_fromRef(v_ref_3021_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3026_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
lean_inc(v___x_3023_);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3023_);
lean_ctor_set(v___x_3027_, 1, v___x_3025_);
lean_ctor_set(v___x_3027_, 2, v___x_3026_);
v___x_3028_ = l_Lean_Syntax_node2(v___x_3023_, v___x_3024_, v___x_3027_, v_a_3020_);
v_a_3013_ = v___x_3028_;
goto v___jp_3012_;
}
else
{
lean_object* v_a_3029_; lean_object* v_ref_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
lean_dec(v_snd_3006_);
v_a_3029_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3018_, 1);
v_ref_3030_ = lean_ctor_get(v___y_2999_, 5);
v___x_3031_ = 0;
v___x_3032_ = l_Lean_SourceInfo_fromRef(v_ref_3030_, v___x_3031_);
v___x_3033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__1));
v___x_3034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___closed__2));
lean_inc(v___x_3032_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 2);
lean_ctor_set(v___x_3008_, 1, v___x_3035_);
lean_ctor_set(v___x_3008_, 0, v___x_3032_);
v___x_3037_ = v___x_3008_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_inc(v___x_3032_);
v___x_3038_ = l_Lean_Syntax_node1(v___x_3032_, v___x_3034_, v___x_3037_);
v___x_3039_ = l_Lean_Syntax_node2(v___x_3032_, v___x_3033_, v___x_3038_, v_a_3029_);
v_a_3013_ = v___x_3039_;
goto v___jp_3012_;
}
}
}
else
{
lean_del_object(v___x_3008_);
lean_dec(v_snd_3006_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3041_; 
v_a_3041_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3018_, 1);
v_a_3013_ = v_a_3041_;
goto v___jp_3012_;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v_bs_x27_3011_);
v_a_3042_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3018_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3018_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
v___jp_3012_:
{
size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = lean_usize_add(v_i_2995_, v___x_3014_);
v___x_3016_ = lean_array_uset(v_bs_x27_3011_, v_i_2995_, v_a_3013_);
v_i_2995_ = v___x_3015_;
v_bs_2996_ = v___x_3016_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object* v_sz_3051_, lean_object* v_i_3052_, lean_object* v_bs_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
size_t v_sz_boxed_3059_; size_t v_i_boxed_3060_; lean_object* v_res_3061_; 
v_sz_boxed_3059_ = lean_unbox_usize(v_sz_3051_);
lean_dec(v_sz_3051_);
v_i_boxed_3060_ = lean_unbox_usize(v_i_3052_);
lean_dec(v_i_3052_);
v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_boxed_3059_, v_i_boxed_3060_, v_bs_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
return v_res_3061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__0));
v___x_3064_ = l_Lean_stringToMessageData(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__2));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Meta_Tactic_TryThis_addSuggestion_spec__0_spec__0___closed__0));
v___x_3069_ = l_Lean_stringToMessageData(v___x_3068_);
return v___x_3069_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__6));
v___x_3074_ = l_Lean_MessageData_ofFormat(v___x_3073_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__8));
v___x_3077_ = l_Lean_stringToMessageData(v___x_3076_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__10));
v___x_3080_ = l_Lean_stringToMessageData(v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object* v___x_3118_, lean_object* v_type_x3f_3119_, lean_object* v_rules_3120_, lean_object* v_loc_x3f_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v_extraMsg_3130_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; size_t v_sz_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v_sz_3175_ = lean_array_size(v___x_3118_);
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(v_sz_3175_, v___x_3176_, v___x_3118_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_a_3182_; lean_object* v_a_3207_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__12));
v___x_3180_ = l_Lean_Syntax_SepArray_ofElems(v___x_3179_, v_a_3178_);
lean_dec(v_a_3178_);
if (lean_obj_tag(v_loc_x3f_3121_) == 0)
{
lean_object* v___x_3209_; 
v___x_3209_ = lean_box(0);
v_a_3182_ = v___x_3209_;
goto v___jp_3181_;
}
else
{
lean_object* v_val_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_val_3210_ = lean_ctor_get(v_loc_x3f_3121_, 0);
v___x_3211_ = lean_box(1);
lean_inc(v_val_3210_);
v___x_3212_ = l_Lean_PrettyPrinter_delab(v_val_3210_, v___x_3211_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v_ref_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v_ref_3214_ = lean_ctor_get(v___y_3124_, 5);
v___x_3215_ = 0;
v___x_3216_ = l_Lean_SourceInfo_fromRef(v_ref_3214_, v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__24));
v___x_3218_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__25));
lean_inc_n(v___x_3216_, 3);
v___x_3219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3216_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__27));
v___x_3221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3222_ = l_Lean_Syntax_node1(v___x_3216_, v___x_3221_, v_a_3213_);
v___x_3223_ = l_Lean_Syntax_node1(v___x_3216_, v___x_3220_, v___x_3222_);
v___x_3224_ = l_Lean_Syntax_node2(v___x_3216_, v___x_3217_, v___x_3219_, v___x_3223_);
v_a_3207_ = v___x_3224_;
goto v___jp_3206_;
}
else
{
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3225_; 
v_a_3225_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3212_, 1);
v_a_3207_ = v_a_3225_;
goto v___jp_3206_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref_known(v_loc_x3f_3121_, 1);
lean_dec_ref(v___x_3180_);
lean_dec(v_rules_3120_);
lean_dec(v_type_x3f_3119_);
v_a_3226_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3212_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3212_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
v___jp_3181_:
{
lean_object* v_ref_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_ref_3183_ = lean_ctor_get(v___y_3124_, 5);
v___x_3184_ = 0;
v___x_3185_ = l_Lean_SourceInfo_fromRef(v_ref_3183_, v___x_3184_);
v___x_3186_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__14));
v___x_3187_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__15));
lean_inc_n(v___x_3185_, 7);
v___x_3188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3185_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__17));
v___x_3190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9));
v___x_3191_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6, &l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___closed__6);
v___x_3192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3185_);
lean_ctor_set(v___x_3192_, 1, v___x_3190_);
lean_ctor_set(v___x_3192_, 2, v___x_3191_);
v___x_3193_ = l_Lean_Syntax_node1(v___x_3185_, v___x_3189_, v___x_3192_);
v___x_3194_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__19));
v___x_3195_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__20));
v___x_3196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3185_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_Array_append___redArg(v___x_3191_, v___x_3180_);
lean_dec_ref(v___x_3180_);
v___x_3198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3185_);
lean_ctor_set(v___x_3198_, 1, v___x_3190_);
lean_ctor_set(v___x_3198_, 2, v___x_3197_);
v___x_3199_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__21));
v___x_3200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3185_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_node3(v___x_3185_, v___x_3194_, v___x_3196_, v___x_3198_, v___x_3200_);
if (lean_obj_tag(v_a_3182_) == 0)
{
lean_object* v___x_3202_; 
v___x_3202_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___y_3150_ = v___x_3186_;
v___y_3151_ = v___x_3201_;
v___y_3152_ = v___x_3191_;
v___y_3153_ = v___x_3190_;
v___y_3154_ = v___x_3193_;
v___y_3155_ = v___x_3185_;
v___y_3156_ = v___x_3188_;
v___y_3157_ = v___x_3202_;
goto v___jp_3149_;
}
else
{
lean_object* v_val_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_val_3203_ = lean_ctor_get(v_a_3182_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v_a_3182_, 1);
v___x_3204_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__22));
v___x_3205_ = lean_array_push(v___x_3204_, v_val_3203_);
v___y_3150_ = v___x_3186_;
v___y_3151_ = v___x_3201_;
v___y_3152_ = v___x_3191_;
v___y_3153_ = v___x_3190_;
v___y_3154_ = v___x_3193_;
v___y_3155_ = v___x_3185_;
v___y_3156_ = v___x_3188_;
v___y_3157_ = v___x_3205_;
goto v___jp_3149_;
}
}
v___jp_3206_:
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_a_3207_);
v_a_3182_ = v___x_3208_;
goto v___jp_3181_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_loc_x3f_3121_);
lean_dec(v_rules_3120_);
lean_dec(v_type_x3f_3119_);
v_a_3234_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3177_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3177_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
v___jp_3127_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___y_3128_);
lean_ctor_set(v___x_3131_, 1, v_extraMsg_3130_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3129_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
v___jp_3134_:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___y_3136_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
switch(lean_obj_tag(v_type_x3f_3119_))
{
case 0:
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref(v___x_3137_);
v___x_3139_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__1);
v___y_3128_ = v_a_3138_;
v___y_3129_ = v___y_3135_;
v_extraMsg_3130_ = v___x_3139_;
goto v___jp_3127_;
}
case 1:
{
lean_object* v_a_3140_; lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_a_3146_; 
v_a_3140_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3137_);
v_a_3141_ = lean_ctor_get(v_type_x3f_3119_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v_type_x3f_3119_, 1);
v___x_3142_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__3);
v___x_3143_ = l_Lean_MessageData_ofExpr(v_a_3141_);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion_spec__0(v___x_3144_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref(v___x_3145_);
v___y_3128_ = v_a_3140_;
v___y_3129_ = v___y_3135_;
v_extraMsg_3130_ = v_a_3146_;
goto v___jp_3127_;
}
default: 
{
lean_object* v_a_3147_; lean_object* v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3147_);
lean_dec_ref(v___x_3137_);
v___x_3148_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__4);
v___y_3128_ = v_a_3147_;
v___y_3129_ = v___y_3135_;
v_extraMsg_3130_ = v___x_3148_;
goto v___jp_3127_;
}
}
}
v___jp_3149_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3158_ = l_Array_append___redArg(v___y_3152_, v___y_3157_);
lean_dec_ref(v___y_3157_);
lean_inc(v___y_3153_);
lean_inc(v___y_3155_);
v___x_3159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3159_, 0, v___y_3155_);
lean_ctor_set(v___x_3159_, 1, v___y_3153_);
lean_ctor_set(v___x_3159_, 2, v___x_3158_);
lean_inc(v___y_3150_);
v___x_3160_ = l_Lean_Syntax_node4(v___y_3155_, v___y_3150_, v___y_3156_, v___y_3154_, v___y_3151_, v___x_3159_);
v___x_3161_ = lean_box(0);
v___x_3162_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(v_rules_3120_, v___x_3161_);
v___x_3163_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__7);
v___x_3164_ = l_Lean_MessageData_joinSep(v___x_3162_, v___x_3163_);
v___x_3165_ = l_Lean_MessageData_sbracket(v___x_3164_);
if (lean_obj_tag(v_loc_x3f_3121_) == 1)
{
lean_object* v_val_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_val_3166_ = lean_ctor_get(v_loc_x3f_3121_, 0);
lean_inc(v_val_3166_);
lean_dec_ref_known(v_loc_x3f_3121_, 1);
v___x_3167_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___x_3165_);
v___x_3169_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__11);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_MessageData_ofExpr(v_val_3166_);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___y_3135_ = v___x_3160_;
v___y_3136_ = v___x_3172_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v_loc_x3f_3121_);
v___x_3173_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___closed__9);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3165_);
v___y_3135_ = v___x_3160_;
v___y_3136_ = v___x_3174_;
goto v___jp_3134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed(lean_object* v___x_3242_, lean_object* v_type_x3f_3243_, lean_object* v_rules_3244_, lean_object* v_loc_x3f_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(v___x_3242_, v_type_x3f_3243_, v_rules_3244_, v_loc_x3f_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3251_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1));
v___x_3256_ = l_Lean_MessageData_ofFormat(v___x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* v_ref_3257_, lean_object* v_rules_3258_, lean_object* v_type_x3f_3259_, lean_object* v_loc_x3f_3260_, lean_object* v_origSpan_x3f_3261_, lean_object* v_checkState_x3f_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; 
lean_inc(v_rules_3258_);
v___x_3272_ = lean_array_mk(v_rules_3258_);
lean_inc(v_type_x3f_3259_);
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3273_, 0, v___x_3272_);
lean_closure_set(v___f_3273_, 1, v_type_x3f_3259_);
lean_closure_set(v___f_3273_, 2, v_rules_3258_);
lean_closure_set(v___f_3273_, 3, v_loc_x3f_3260_);
v___x_3274_ = l_Lean_Meta_withExposedNames___redArg(v___f_3273_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v_snd_3276_; lean_object* v_fst_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3348_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v_snd_3276_ = lean_ctor_get(v_a_3275_, 1);
v_fst_3277_ = lean_ctor_get(v_a_3275_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_a_3275_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3279_ = v_a_3275_;
v_isShared_3280_ = v_isSharedCheck_3348_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_snd_3276_);
lean_inc(v_fst_3277_);
lean_dec(v_a_3275_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3348_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3347_; 
v_fst_3281_ = lean_ctor_get(v_snd_3276_, 0);
v_snd_3282_ = lean_ctor_get(v_snd_3276_, 1);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_snd_3276_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3284_ = v_snd_3276_;
v_isShared_3285_ = v_isSharedCheck_3347_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_dec(v_snd_3276_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3347_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_tac_3287_; lean_object* v_tacMsg_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; 
if (lean_obj_tag(v_checkState_x3f_3262_) == 1)
{
lean_object* v_val_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3346_; 
v_val_3305_ = lean_ctor_get(v_checkState_x3f_3262_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_checkState_x3f_3262_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3307_ = v_checkState_x3f_3262_;
v_isShared_3308_ = v_isSharedCheck_3346_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_val_3305_);
lean_dec(v_checkState_x3f_3262_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3346_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___y_3310_; 
if (lean_obj_tag(v_type_x3f_3259_) == 1)
{
lean_object* v_a_3341_; lean_object* v___x_3343_; 
v_a_3341_ = lean_ctor_get(v_type_x3f_3259_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v_type_x3f_3259_, 1);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v_a_3341_);
v___x_3343_ = v___x_3307_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
v___y_3310_ = v___x_3343_;
goto v___jp_3309_;
}
}
else
{
lean_object* v___x_3345_; 
lean_del_object(v___x_3307_);
lean_dec(v_type_x3f_3259_);
v___x_3345_ = lean_box(0);
v___y_3310_ = v___x_3345_;
goto v___jp_3309_;
}
v___jp_3309_:
{
lean_object* v___x_3311_; 
lean_inc(v_fst_3281_);
v___x_3311_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(v_fst_3277_, v_fst_3281_, v_val_3305_, v___y_3310_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
if (lean_obj_tag(v_a_3312_) == 1)
{
lean_object* v_val_3313_; lean_object* v_fst_3314_; lean_object* v_snd_3315_; 
lean_dec(v_fst_3281_);
v_val_3313_ = lean_ctor_get(v_a_3312_, 0);
lean_inc(v_val_3313_);
lean_dec_ref_known(v_a_3312_, 1);
v_fst_3314_ = lean_ctor_get(v_val_3313_, 0);
lean_inc(v_fst_3314_);
v_snd_3315_ = lean_ctor_get(v_val_3313_, 1);
lean_inc(v_snd_3315_);
lean_dec(v_val_3313_);
v_tac_3287_ = v_fst_3314_;
v_tacMsg_3288_ = v_snd_3315_;
v___y_3289_ = v_a_3269_;
v___y_3290_ = v_a_3270_;
goto v___jp_3286_;
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v_a_3312_);
lean_del_object(v___x_3284_);
lean_del_object(v___x_3279_);
lean_dec(v_origSpan_x3f_3261_);
lean_dec(v_ref_3257_);
v___x_3316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v_fst_3281_);
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17, &l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17_once, _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2, &l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2_once, _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v_snd_3282_);
v___x_3322_ = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(v___x_3320_, v___x_3321_);
v___x_3323_ = l_Lean_logInfo___at___00Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(v___x_3322_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3331_; 
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v___x_3323_, 0);
lean_dec(v_unused_3332_);
v___x_3325_ = v___x_3323_;
v_isShared_3326_ = v_isSharedCheck_3331_;
goto v_resetjp_3324_;
}
else
{
lean_dec(v___x_3323_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3331_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3327_ = lean_box(0);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3327_);
v___x_3329_ = v___x_3325_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
return v___x_3323_;
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_dec(v_fst_3281_);
lean_del_object(v___x_3279_);
lean_dec(v_origSpan_x3f_3261_);
lean_dec(v_ref_3257_);
v_a_3333_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3311_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3311_);
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
}
else
{
lean_dec(v_checkState_x3f_3262_);
lean_dec(v_type_x3f_3259_);
v_tac_3287_ = v_fst_3277_;
v_tacMsg_3288_ = v_fst_3281_;
v___y_3289_ = v_a_3269_;
v___y_3290_ = v_a_3270_;
goto v___jp_3286_;
}
v___jp_3286_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___closed__1));
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v_tac_3287_);
lean_ctor_set(v___x_3284_, 0, v___x_3291_);
v___x_3293_ = v___x_3284_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_tac_3287_);
v___x_3293_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3294_ = lean_box(0);
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 7);
lean_ctor_set(v___x_3279_, 1, v_snd_3282_);
lean_ctor_set(v___x_3279_, 0, v_tacMsg_3288_);
v___x_3296_ = v___x_3279_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_tacMsg_3288_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_snd_3282_);
v___x_3296_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3293_);
lean_ctor_set(v___x_3298_, 1, v___x_3294_);
lean_ctor_set(v___x_3298_, 2, v___x_3294_);
lean_ctor_set(v___x_3298_, 3, v___x_3294_);
lean_ctor_set(v___x_3298_, 4, v___x_3297_);
lean_ctor_set(v___x_3298_, 5, v___x_3294_);
v___x_3299_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_addExactSuggestion___closed__0));
v___x_3300_ = 4;
v___x_3301_ = l_Lean_MessageData_nil;
v___x_3302_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3257_, v___x_3298_, v_origSpan_x3f_3261_, v___x_3299_, v___x_3294_, v___x_3300_, v___x_3301_, v___y_3289_, v___y_3290_);
return v___x_3302_;
}
}
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_checkState_x3f_3262_);
lean_dec(v_origSpan_x3f_3261_);
lean_dec(v_type_x3f_3259_);
lean_dec(v_ref_3257_);
v_a_3349_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3274_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3274_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object* v_ref_3357_, lean_object* v_rules_3358_, lean_object* v_type_x3f_3359_, lean_object* v_loc_x3f_3360_, lean_object* v_origSpan_x3f_3361_, lean_object* v_checkState_x3f_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3357_, v_rules_3358_, v_type_x3f_3359_, v_loc_x3f_3360_, v_origSpan_x3f_3361_, v_checkState_x3f_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
return v_res_3372_;
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
