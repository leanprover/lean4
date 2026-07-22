// Lean compiler output
// Module: Lake.DSL.Meta
// Imports: public import Lean.ToExpr import Lean.Elab.Eval import Lake.DSL.Syntax
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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_evalTerm___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
extern lean_object* l_ByteArray_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
lean_object* lean_get_set_stdin(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cmdDo"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__2_value),LEAN_SCALAR_PTR_LITERAL(97, 39, 184, 30, 65, 63, 201, 66)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3_value;
static const lean_array_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__5_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(lean_object*);
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1_value;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "metaIf"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 98, 156, 191, 205, 206, 20, 202)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "ill-formed meta if command"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__1_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(136, 32, 184, 223, 75, 60, 76, 140)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(225, 114, 74, 217, 10, 225, 148, 209)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 164, 27, 163, 115, 248, 126, 206)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(234, 137, 163, 198, 219, 182, 58, 201)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMetaIf"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(137, 140, 51, 207, 254, 31, 199, 80)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IO"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 76, 19, 202, 4, 69, 238, 60)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1_value;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5_value;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3_value;
static lean_once_cell_t l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "runIO"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 189, 119, 141, 116, 67, 96, 12)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1_value;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toExprIO"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value),LEAN_SCALAR_PTR_LITERAL(100, 226, 78, 143, 214, 112, 160, 165)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_2),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabRunIO"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 107, 238, 192, 2, 123, 75, 134)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(lean_object* v_x_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__3));
lean_inc(v_x_13_);
v___x_15_ = l_Lean_Syntax_isOfKind(v_x_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_dec(v_x_13_);
v___x_16_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__4));
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v_cmd_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_cmd_18_ = l_Lean_Syntax_getArg(v_x_13_, v___x_17_);
lean_dec(v_x_13_);
v___x_19_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__6));
lean_inc(v_cmd_18_);
v___x_20_ = l_Lean_Syntax_isOfKind(v_cmd_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_mk_empty_array_with_capacity(v___x_21_);
v___x_23_ = lean_array_push(v___x_22_, v_cmd_18_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = l_Lean_Syntax_getArg(v_cmd_18_, v___x_24_);
lean_dec(v_cmd_18_);
v___x_26_ = l_Lean_Syntax_getArgs(v___x_25_);
lean_dec(v___x_25_);
return v___x_26_;
}
}
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(0);
v___x_31_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__1));
v___x_32_ = l_Lean_mkConst(v___x_31_, v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(lean_object* v_c_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2);
v___x_42_ = 0;
v___x_43_ = l_Lean_Elab_Term_evalTerm___redArg(v___x_41_, v_c_33_, v___x_42_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___boxed(lean_object* v_c_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(v_c_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(lean_object* v___x_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2);
v___x_63_ = 0;
v___x_64_ = l_Lean_Elab_Term_evalTerm___redArg(v___x_62_, v___x_53_, v___x_63_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed(lean_object* v___x_65_, lean_object* v_x_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(v___x_65_, v_x_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec_ref(v_x_66_);
return v_res_74_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(1);
v___x_76_ = l_Lean_MessageData_ofFormat(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_81_ = l_Lean_MessageData_ofFormat(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
return v_x_82_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_107_; 
v_head_84_ = lean_ctor_get(v_x_83_, 0);
v_tail_85_ = lean_ctor_get(v_x_83_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_107_ == 0)
{
v___x_87_ = v_x_83_;
v_isShared_88_ = v_isSharedCheck_107_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_tail_85_);
lean_inc(v_head_84_);
lean_dec(v_x_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_107_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_before_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_105_; 
v_before_89_ = lean_ctor_get(v_head_84_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_head_84_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v_head_84_, 1);
lean_dec(v_unused_106_);
v___x_91_ = v_head_84_;
v_isShared_92_ = v_isSharedCheck_105_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_before_89_);
lean_dec(v_head_84_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_105_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 7);
lean_ctor_set(v___x_91_, 1, v___x_93_);
lean_ctor_set(v___x_91_, 0, v_x_82_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_x_82_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_104_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 7);
lean_ctor_set(v___x_87_, 1, v___x_96_);
lean_ctor_set(v___x_87_, 0, v___x_95_);
v___x_98_ = v___x_87_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_103_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = l_Lean_MessageData_ofSyntax(v_before_89_);
v___x_100_ = l_Lean_indentD(v___x_99_);
v___x_101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_98_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v_x_82_ = v___x_101_;
v_x_83_ = v_tail_85_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(lean_object* v_opts_108_, lean_object* v_opt_109_){
_start:
{
lean_object* v_name_110_; lean_object* v_defValue_111_; lean_object* v_map_112_; lean_object* v___x_113_; 
v_name_110_ = lean_ctor_get(v_opt_109_, 0);
v_defValue_111_ = lean_ctor_get(v_opt_109_, 1);
v_map_112_ = lean_ctor_get(v_opts_108_, 0);
v___x_113_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_112_, v_name_110_);
if (lean_obj_tag(v___x_113_) == 0)
{
uint8_t v___x_114_; 
v___x_114_ = lean_unbox(v_defValue_111_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; 
v_val_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v___x_113_, 1);
if (lean_obj_tag(v_val_115_) == 1)
{
uint8_t v_v_116_; 
v_v_116_ = lean_ctor_get_uint8(v_val_115_, 0);
lean_dec_ref_known(v_val_115_, 0);
return v_v_116_;
}
else
{
uint8_t v___x_117_; 
lean_dec(v_val_115_);
v___x_117_ = lean_unbox(v_defValue_111_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_118_, v_opt_119_);
lean_dec_ref(v_opt_119_);
lean_dec_ref(v_opts_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_126_ = l_Lean_MessageData_ofFormat(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_127_, lean_object* v_macroStack_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; lean_object* v_scopes_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_opts_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_131_ = lean_st_ref_get(v___y_129_);
v_scopes_132_ = lean_ctor_get(v___x_131_, 2);
lean_inc(v_scopes_132_);
lean_dec(v___x_131_);
v___x_133_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_134_ = l_List_head_x21___redArg(v___x_133_, v_scopes_132_);
lean_dec(v_scopes_132_);
v_opts_135_ = lean_ctor_get(v___x_134_, 1);
lean_inc_ref(v_opts_135_);
lean_dec(v___x_134_);
v___x_136_ = l_Lean_Elab_pp_macroStack;
v___x_137_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_135_, v___x_136_);
lean_dec_ref(v_opts_135_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_dec(v_macroStack_128_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_msgData_127_);
return v___x_138_;
}
else
{
if (lean_obj_tag(v_macroStack_128_) == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_msgData_127_);
return v___x_139_;
}
else
{
lean_object* v_head_140_; lean_object* v_after_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_156_; 
v_head_140_ = lean_ctor_get(v_macroStack_128_, 0);
lean_inc(v_head_140_);
v_after_141_ = lean_ctor_get(v_head_140_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_head_140_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_head_140_, 0);
lean_dec(v_unused_157_);
v___x_143_ = v_head_140_;
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_after_141_);
lean_dec(v_head_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 7);
lean_ctor_set(v___x_143_, 1, v___x_145_);
lean_ctor_set(v___x_143_, 0, v_msgData_127_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_msgData_127_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_155_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_msgData_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_148_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = l_Lean_MessageData_ofSyntax(v_after_141_);
v___x_151_ = l_Lean_indentD(v___x_150_);
v_msgData_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_152_, 0, v___x_149_);
lean_ctor_set(v_msgData_152_, 1, v___x_151_);
v___x_153_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(v_msgData_152_, v_macroStack_128_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_158_, lean_object* v_macroStack_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_158_, v_macroStack_159_, v___y_160_);
lean_dec(v___y_160_);
return v_res_162_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_ctor_set(v___x_168_, 2, v___x_167_);
lean_ctor_set(v___x_168_, 3, v___x_167_);
lean_ctor_set(v___x_168_, 4, v___x_166_);
lean_ctor_set(v___x_168_, 5, v___x_166_);
lean_ctor_set(v___x_168_, 6, v___x_166_);
lean_ctor_set(v___x_168_, 7, v___x_166_);
lean_ctor_set(v___x_168_, 8, v___x_166_);
lean_ctor_set(v___x_168_, 9, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(32u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_unsigned_to_nat(32u);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_177_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_173_);
lean_ctor_set(v___x_177_, 3, v___x_173_);
lean_ctor_set_usize(v___x_177_, 4, v___x_172_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = lean_box(1);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v_env_186_; lean_object* v___x_187_; lean_object* v_scopes_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_opts_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_185_ = lean_st_ref_get(v___y_183_);
v_env_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc_ref(v_env_186_);
lean_dec(v___x_185_);
v___x_187_ = lean_st_ref_get(v___y_183_);
v_scopes_188_ = lean_ctor_get(v___x_187_, 2);
lean_inc(v_scopes_188_);
lean_dec(v___x_187_);
v___x_189_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_190_ = l_List_head_x21___redArg(v___x_189_, v_scopes_188_);
lean_dec(v_scopes_188_);
v_opts_191_ = lean_ctor_get(v___x_190_, 1);
lean_inc_ref(v_opts_191_);
lean_dec(v___x_190_);
v___x_192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_194_, 0, v_env_186_);
lean_ctor_set(v___x_194_, 1, v___x_192_);
lean_ctor_set(v___x_194_, 2, v___x_193_);
lean_ctor_set(v___x_194_, 3, v_opts_191_);
v___x_195_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_msgData_182_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_197_, v___y_198_);
lean_dec(v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Elab_Command_getRef___redArg(v___y_202_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_macroStack_207_; lean_object* v___x_208_; lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v_macroStack_207_ = lean_ctor_get(v___y_202_, 4);
v___x_208_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msg_201_, v___y_203_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
v___x_210_ = l_Lean_Elab_getBetterRef(v_a_206_, v_macroStack_207_);
lean_dec(v_a_206_);
lean_inc(v_macroStack_207_);
v___x_211_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_a_209_, v_macroStack_207_, v___y_203_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_210_);
lean_ctor_set(v___x_216_, 1, v_a_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 1);
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_msg_201_);
v_a_221_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_205_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_205_);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg___boxed(lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(lean_object* v_ref_234_, lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Elab_Command_getRef___redArg(v___y_236_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v_fileName_241_; lean_object* v_fileMap_242_; lean_object* v_currRecDepth_243_; lean_object* v_cmdPos_244_; lean_object* v_macroStack_245_; lean_object* v_quotContext_x3f_246_; lean_object* v_currMacroScope_247_; lean_object* v_snap_x3f_248_; lean_object* v_cancelTk_x3f_249_; uint8_t v_suppressElabErrors_250_; lean_object* v_ref_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v_fileName_241_ = lean_ctor_get(v___y_236_, 0);
v_fileMap_242_ = lean_ctor_get(v___y_236_, 1);
v_currRecDepth_243_ = lean_ctor_get(v___y_236_, 2);
v_cmdPos_244_ = lean_ctor_get(v___y_236_, 3);
v_macroStack_245_ = lean_ctor_get(v___y_236_, 4);
v_quotContext_x3f_246_ = lean_ctor_get(v___y_236_, 5);
v_currMacroScope_247_ = lean_ctor_get(v___y_236_, 6);
v_snap_x3f_248_ = lean_ctor_get(v___y_236_, 8);
v_cancelTk_x3f_249_ = lean_ctor_get(v___y_236_, 9);
v_suppressElabErrors_250_ = lean_ctor_get_uint8(v___y_236_, sizeof(void*)*10);
v_ref_251_ = l_Lean_replaceRef(v_ref_234_, v_a_240_);
lean_dec(v_a_240_);
lean_inc(v_cancelTk_x3f_249_);
lean_inc(v_snap_x3f_248_);
lean_inc(v_currMacroScope_247_);
lean_inc(v_quotContext_x3f_246_);
lean_inc(v_macroStack_245_);
lean_inc(v_cmdPos_244_);
lean_inc(v_currRecDepth_243_);
lean_inc_ref(v_fileMap_242_);
lean_inc_ref(v_fileName_241_);
v___x_252_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_252_, 0, v_fileName_241_);
lean_ctor_set(v___x_252_, 1, v_fileMap_242_);
lean_ctor_set(v___x_252_, 2, v_currRecDepth_243_);
lean_ctor_set(v___x_252_, 3, v_cmdPos_244_);
lean_ctor_set(v___x_252_, 4, v_macroStack_245_);
lean_ctor_set(v___x_252_, 5, v_quotContext_x3f_246_);
lean_ctor_set(v___x_252_, 6, v_currMacroScope_247_);
lean_ctor_set(v___x_252_, 7, v_ref_251_);
lean_ctor_set(v___x_252_, 8, v_snap_x3f_248_);
lean_ctor_set(v___x_252_, 9, v_cancelTk_x3f_249_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*10, v_suppressElabErrors_250_);
v___x_253_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_235_, v___x_252_, v___y_237_);
lean_dec_ref_known(v___x_252_, 10);
return v___x_253_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_msg_235_);
v_a_254_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_239_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_239_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg___boxed(lean_object* v_ref_262_, lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_262_, v_msg_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v_ref_262_);
return v_res_267_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(lean_object* v_stx_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1));
lean_inc(v_stx_279_);
v___x_284_ = l_Lean_Syntax_isOfKind(v_stx_279_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3);
v___x_286_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_stx_279_, v___x_285_, v_a_280_, v_a_281_);
lean_dec(v_stx_279_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v_t_291_; lean_object* v_e_x3f_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_287_ = lean_unsigned_to_nat(2u);
v___x_288_ = l_Lean_Syntax_getArg(v_stx_279_, v___x_287_);
lean_inc(v___x_288_);
v___f_289_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed), 9, 1);
lean_closure_set(v___f_289_, 0, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(4u);
v_t_291_ = l_Lean_Syntax_getArg(v_stx_279_, v___x_290_);
v___x_370_ = lean_unsigned_to_nat(5u);
v___x_371_ = l_Lean_Syntax_getArg(v_stx_279_, v___x_370_);
v___x_372_ = l_Lean_Syntax_isNone(v___x_371_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; 
lean_inc(v___x_371_);
v___x_373_ = l_Lean_Syntax_matchesNull(v___x_371_, v___x_287_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v___x_371_);
lean_dec(v_t_291_);
lean_dec_ref(v___f_289_);
lean_dec(v___x_288_);
v___x_374_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3);
v___x_375_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_stx_279_, v___x_374_, v_a_280_, v_a_281_);
lean_dec(v_stx_279_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; lean_object* v_e_x3f_377_; lean_object* v___x_378_; 
lean_dec(v_stx_279_);
v___x_376_ = lean_unsigned_to_nat(1u);
v_e_x3f_377_ = l_Lean_Syntax_getArg(v___x_371_, v___x_376_);
lean_dec(v___x_371_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_e_x3f_377_);
v_e_x3f_293_ = v___x_378_;
v___y_294_ = v_a_280_;
v___y_295_ = v_a_281_;
goto v___jp_292_;
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_371_);
lean_dec(v_stx_279_);
v___x_379_ = lean_box(0);
v_e_x3f_293_ = v___x_379_;
v___y_294_ = v_a_280_;
v___y_295_ = v_a_281_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Elab_Command_getRef___redArg(v___y_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v_fileName_298_; lean_object* v_fileMap_299_; lean_object* v_currRecDepth_300_; lean_object* v_cmdPos_301_; lean_object* v_macroStack_302_; lean_object* v_quotContext_x3f_303_; lean_object* v_currMacroScope_304_; lean_object* v_snap_x3f_305_; lean_object* v_cancelTk_x3f_306_; uint8_t v_suppressElabErrors_307_; lean_object* v_ref_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v_fileName_298_ = lean_ctor_get(v___y_294_, 0);
v_fileMap_299_ = lean_ctor_get(v___y_294_, 1);
v_currRecDepth_300_ = lean_ctor_get(v___y_294_, 2);
v_cmdPos_301_ = lean_ctor_get(v___y_294_, 3);
v_macroStack_302_ = lean_ctor_get(v___y_294_, 4);
v_quotContext_x3f_303_ = lean_ctor_get(v___y_294_, 5);
v_currMacroScope_304_ = lean_ctor_get(v___y_294_, 6);
v_snap_x3f_305_ = lean_ctor_get(v___y_294_, 8);
v_cancelTk_x3f_306_ = lean_ctor_get(v___y_294_, 9);
v_suppressElabErrors_307_ = lean_ctor_get_uint8(v___y_294_, sizeof(void*)*10);
v_ref_308_ = l_Lean_replaceRef(v___x_288_, v_a_297_);
lean_dec(v_a_297_);
lean_dec(v___x_288_);
lean_inc(v_cancelTk_x3f_306_);
lean_inc(v_snap_x3f_305_);
lean_inc(v_currMacroScope_304_);
lean_inc(v_quotContext_x3f_303_);
lean_inc(v_macroStack_302_);
lean_inc(v_cmdPos_301_);
lean_inc(v_currRecDepth_300_);
lean_inc_ref(v_fileMap_299_);
lean_inc_ref(v_fileName_298_);
v___x_309_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_309_, 0, v_fileName_298_);
lean_ctor_set(v___x_309_, 1, v_fileMap_299_);
lean_ctor_set(v___x_309_, 2, v_currRecDepth_300_);
lean_ctor_set(v___x_309_, 3, v_cmdPos_301_);
lean_ctor_set(v___x_309_, 4, v_macroStack_302_);
lean_ctor_set(v___x_309_, 5, v_quotContext_x3f_303_);
lean_ctor_set(v___x_309_, 6, v_currMacroScope_304_);
lean_ctor_set(v___x_309_, 7, v_ref_308_);
lean_ctor_set(v___x_309_, 8, v_snap_x3f_305_);
lean_ctor_set(v___x_309_, 9, v_cancelTk_x3f_306_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*10, v_suppressElabErrors_307_);
v___x_310_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_289_, v___x_309_, v___y_295_);
lean_dec_ref_known(v___x_309_, 10);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_353_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_353_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_353_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_353_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; 
v___x_315_ = lean_unbox(v_a_311_);
lean_dec(v_a_311_);
if (v___x_315_ == 0)
{
lean_dec(v_t_291_);
if (lean_obj_tag(v_e_x3f_293_) == 1)
{
lean_object* v_val_316_; lean_object* v___x_317_; 
lean_del_object(v___x_313_);
v_val_316_ = lean_ctor_get(v_e_x3f_293_, 0);
lean_inc(v_val_316_);
lean_dec_ref_known(v_e_x3f_293_, 1);
v___x_317_ = l_Lean_Elab_Command_getRef___redArg(v___y_294_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v___x_319_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(v_val_316_);
v___x_320_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5));
v___x_321_ = lean_box(2);
v___x_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_319_);
lean_inc_ref(v___x_322_);
v___x_323_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_323_, 0, v___x_322_);
v___x_324_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_a_318_, v___x_322_, v___x_323_, v___y_294_, v___y_295_);
return v___x_324_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v_val_316_);
v_a_325_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_317_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_317_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec(v_e_x3f_293_);
v___x_333_ = lean_box(0);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_333_);
v___x_335_ = v___x_313_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v___x_337_; 
lean_del_object(v___x_313_);
lean_dec(v_e_x3f_293_);
v___x_337_ = l_Lean_Elab_Command_getRef___redArg(v___y_294_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(v_t_291_);
v___x_340_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5));
v___x_341_ = lean_box(2);
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_339_);
lean_inc_ref(v___x_342_);
v___x_343_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_343_, 0, v___x_342_);
v___x_344_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_a_338_, v___x_342_, v___x_343_, v___y_294_, v___y_295_);
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_t_291_);
v_a_345_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_337_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_337_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_e_x3f_293_);
lean_dec(v_t_291_);
v_a_354_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_310_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_310_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_e_x3f_293_);
lean_dec(v_t_291_);
lean_dec_ref(v___f_289_);
lean_dec(v___x_288_);
v_a_362_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_296_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_296_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed(lean_object* v_stx_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(v_stx_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(lean_object* v_00_u03b1_385_, lean_object* v_ref_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_386_, v_msg_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___boxed(lean_object* v_00_u03b1_392_, lean_object* v_ref_393_, lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(v_00_u03b1_392_, v_ref_393_, v_msg_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v_ref_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(lean_object* v_msgData_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_399_, v___y_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(v_msgData_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(lean_object* v_00_u03b1_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_410_, v___y_411_, v___y_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___boxed(lean_object* v_00_u03b1_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(v_00_u03b1_415_, v_msg_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(lean_object* v_msgData_421_, lean_object* v_macroStack_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_421_, v_macroStack_422_, v___y_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_427_, lean_object* v_macroStack_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(v_msgData_427_, v_macroStack_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1(){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_461_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_462_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1));
v___x_463_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10));
v___x_464_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed), 4, 0);
v___x_465_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_461_, v___x_462_, v___x_463_, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___boxed(lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___redArg(lean_object* v_inst_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_toExpr_471_; lean_object* v___x_472_; 
v_toExpr_471_ = lean_ctor_get(v_inst_468_, 0);
lean_inc_ref(v_toExpr_471_);
lean_dec_ref(v_inst_468_);
v___x_472_ = lean_apply_1(v_x_469_, lean_box(0));
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = lean_apply_1(v_toExpr_471_, v_a_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v_toExpr_471_);
v_a_482_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_472_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_472_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___redArg___boxed(lean_object* v_inst_490_, lean_object* v_x_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lake_DSL_toExprIO___redArg(v_inst_490_, v_x_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO(lean_object* v_00_u03b1_494_, lean_object* v_inst_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lake_DSL_toExprIO___redArg(v_inst_495_, v_x_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___boxed(lean_object* v_00_u03b1_499_, lean_object* v_inst_500_, lean_object* v_x_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_DSL_toExprIO(v_00_u03b1_499_, v_inst_500_, v_x_501_);
return v_res_503_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
v___x_508_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1));
v___x_509_ = l_Lean_mkConst(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_box(0);
v___x_516_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5));
v___x_517_ = l_Lean_mkConst(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6);
v___x_519_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2);
v___x_520_ = l_Lean_Expr_app___override(v___x_519_, v___x_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(lean_object* v_v_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; uint8_t v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; 
v___x_527_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7);
v___x_528_ = 1;
v___x_529_ = 1;
v___x_530_ = l_Lean_Meta_evalExpr___redArg(v___x_527_, v_v_521_, v___x_528_, v___x_529_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___boxed(lean_object* v_v_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(v_v_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_537_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_box(0);
v___x_539_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg(){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___boxed(lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(lean_object* v_00_u03b1_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___boxed(lean_object* v_00_u03b1_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(v_00_u03b1_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(lean_object* v_e_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Expr_hasMVar(v_e_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_e_564_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v_mctx_570_; lean_object* v___x_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_574_; lean_object* v_cache_575_; lean_object* v_zetaDeltaFVarIds_576_; lean_object* v_postponed_577_; lean_object* v_diag_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_587_; 
v___x_569_ = lean_st_ref_get(v___y_565_);
v_mctx_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_mctx_570_);
lean_dec(v___x_569_);
v___x_571_ = l_Lean_instantiateMVarsCore(v_mctx_570_, v_e_564_);
v_fst_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_573_);
lean_dec_ref(v___x_571_);
v___x_574_ = lean_st_ref_take(v___y_565_);
v_cache_575_ = lean_ctor_get(v___x_574_, 1);
v_zetaDeltaFVarIds_576_ = lean_ctor_get(v___x_574_, 2);
v_postponed_577_ = lean_ctor_get(v___x_574_, 3);
v_diag_578_ = lean_ctor_get(v___x_574_, 4);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_574_, 0);
lean_dec(v_unused_588_);
v___x_580_ = v___x_574_;
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_diag_578_);
lean_inc(v_postponed_577_);
lean_inc(v_zetaDeltaFVarIds_576_);
lean_inc(v_cache_575_);
lean_dec(v___x_574_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_snd_573_);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_snd_573_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_cache_575_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_zetaDeltaFVarIds_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_postponed_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_diag_578_);
v___x_583_ = v_reuseFailAlloc_586_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_st_ref_set(v___y_565_, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v_fst_572_);
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg___boxed(lean_object* v_e_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_589_, v___y_590_);
lean_dec(v___y_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(lean_object* v_e_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_593_, v___y_597_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___boxed(lean_object* v_e_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(v_e_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_610_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_box(0);
v___x_612_ = l_Lean_Elab_abortTermExceptionId;
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg(){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___boxed(lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(lean_object* v_00_u03b1_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___boxed(lean_object* v_00_u03b1_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(v_00_u03b1_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(lean_object* v_a_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_apply_1(v_a_637_, lean_box(0));
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v_a_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_a_655_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_645_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_645_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 0);
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed(lean_object* v_a_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(v_a_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(lean_object* v_msgData_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v_env_680_; lean_object* v___x_681_; lean_object* v_mctx_682_; lean_object* v_lctx_683_; lean_object* v_options_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_679_ = lean_st_ref_get(v___y_677_);
v_env_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_ref(v_env_680_);
lean_dec(v___x_679_);
v___x_681_ = lean_st_ref_get(v___y_675_);
v_mctx_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_mctx_682_);
lean_dec(v___x_681_);
v_lctx_683_ = lean_ctor_get(v___y_674_, 2);
v_options_684_ = lean_ctor_get(v___y_676_, 2);
lean_inc_ref(v_options_684_);
lean_inc_ref(v_lctx_683_);
v___x_685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_685_, 0, v_env_680_);
lean_ctor_set(v___x_685_, 1, v_mctx_682_);
lean_ctor_set(v___x_685_, 2, v_lctx_683_);
lean_ctor_set(v___x_685_, 3, v_options_684_);
v___x_686_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v_msgData_673_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9___boxed(lean_object* v_msgData_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msgData_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(uint8_t v___y_703_, uint8_t v_suppressElabErrors_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_705_) == 1)
{
lean_object* v_pre_706_; 
v_pre_706_ = lean_ctor_get(v_x_705_, 0);
switch(lean_obj_tag(v_pre_706_))
{
case 1:
{
lean_object* v_pre_707_; 
v_pre_707_ = lean_ctor_get(v_pre_706_, 0);
switch(lean_obj_tag(v_pre_707_))
{
case 0:
{
lean_object* v_str_708_; lean_object* v_str_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_str_708_ = lean_ctor_get(v_x_705_, 1);
v_str_709_ = lean_ctor_get(v_pre_706_, 1);
v___x_710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0));
v___x_711_ = lean_string_dec_eq(v_str_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1));
v___x_713_ = lean_string_dec_eq(v_str_709_, v___x_712_);
if (v___x_713_ == 0)
{
return v___y_703_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2));
v___x_715_ = lean_string_dec_eq(v_str_708_, v___x_714_);
if (v___x_715_ == 0)
{
return v___y_703_;
}
else
{
return v_suppressElabErrors_704_;
}
}
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3));
v___x_717_ = lean_string_dec_eq(v_str_708_, v___x_716_);
if (v___x_717_ == 0)
{
return v___y_703_;
}
else
{
return v_suppressElabErrors_704_;
}
}
}
case 1:
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_pre_707_, 0);
if (lean_obj_tag(v_pre_718_) == 0)
{
lean_object* v_str_719_; lean_object* v_str_720_; lean_object* v_str_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_str_719_ = lean_ctor_get(v_x_705_, 1);
v_str_720_ = lean_ctor_get(v_pre_706_, 1);
v_str_721_ = lean_ctor_get(v_pre_707_, 1);
v___x_722_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4));
v___x_723_ = lean_string_dec_eq(v_str_721_, v___x_722_);
if (v___x_723_ == 0)
{
return v___y_703_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5));
v___x_725_ = lean_string_dec_eq(v_str_720_, v___x_724_);
if (v___x_725_ == 0)
{
return v___y_703_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6));
v___x_727_ = lean_string_dec_eq(v_str_719_, v___x_726_);
if (v___x_727_ == 0)
{
return v___y_703_;
}
else
{
return v_suppressElabErrors_704_;
}
}
}
}
else
{
return v___y_703_;
}
}
default: 
{
return v___y_703_;
}
}
}
case 0:
{
lean_object* v_str_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_str_728_ = lean_ctor_get(v_x_705_, 1);
v___x_729_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7));
v___x_730_ = lean_string_dec_eq(v_str_728_, v___x_729_);
if (v___x_730_ == 0)
{
return v___y_703_;
}
else
{
return v_suppressElabErrors_704_;
}
}
default: 
{
return v___y_703_;
}
}
}
else
{
return v___y_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed(lean_object* v___y_731_, lean_object* v_suppressElabErrors_732_, lean_object* v_x_733_){
_start:
{
uint8_t v___y_23286__boxed_734_; uint8_t v_suppressElabErrors_boxed_735_; uint8_t v_res_736_; lean_object* v_r_737_; 
v___y_23286__boxed_734_ = lean_unbox(v___y_731_);
v_suppressElabErrors_boxed_735_ = lean_unbox(v_suppressElabErrors_732_);
v_res_736_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(v___y_23286__boxed_734_, v_suppressElabErrors_boxed_735_, v_x_733_);
lean_dec(v_x_733_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(lean_object* v_ref_739_, lean_object* v_msgData_740_, uint8_t v_severity_741_, uint8_t v_isSilent_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___y_749_; lean_object* v___y_750_; uint8_t v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; uint8_t v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; lean_object* v___y_810_; lean_object* v___y_811_; uint8_t v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; uint8_t v___y_816_; lean_object* v___y_817_; lean_object* v___y_821_; uint8_t v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; uint8_t v___x_832_; uint8_t v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; uint8_t v___y_840_; uint8_t v___y_842_; uint8_t v___x_857_; 
v___x_832_ = 2;
v___x_857_ = l_Lean_instBEqMessageSeverity_beq(v_severity_741_, v___x_832_);
if (v___x_857_ == 0)
{
v___y_842_ = v___x_857_;
goto v___jp_841_;
}
else
{
uint8_t v___x_858_; 
lean_inc_ref(v_msgData_740_);
v___x_858_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_740_);
v___y_842_ = v___x_858_;
goto v___jp_841_;
}
v___jp_748_:
{
lean_object* v___x_758_; lean_object* v_currNamespace_759_; lean_object* v_openDecls_760_; lean_object* v_env_761_; lean_object* v_nextMacroScope_762_; lean_object* v_ngen_763_; lean_object* v_auxDeclNGen_764_; lean_object* v_traceState_765_; lean_object* v_cache_766_; lean_object* v_messages_767_; lean_object* v_infoState_768_; lean_object* v_snapshotTasks_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_783_; 
v___x_758_ = lean_st_ref_take(v___y_757_);
v_currNamespace_759_ = lean_ctor_get(v___y_756_, 6);
v_openDecls_760_ = lean_ctor_get(v___y_756_, 7);
v_env_761_ = lean_ctor_get(v___x_758_, 0);
v_nextMacroScope_762_ = lean_ctor_get(v___x_758_, 1);
v_ngen_763_ = lean_ctor_get(v___x_758_, 2);
v_auxDeclNGen_764_ = lean_ctor_get(v___x_758_, 3);
v_traceState_765_ = lean_ctor_get(v___x_758_, 4);
v_cache_766_ = lean_ctor_get(v___x_758_, 5);
v_messages_767_ = lean_ctor_get(v___x_758_, 6);
v_infoState_768_ = lean_ctor_get(v___x_758_, 7);
v_snapshotTasks_769_ = lean_ctor_get(v___x_758_, 8);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_783_ == 0)
{
v___x_771_ = v___x_758_;
v_isShared_772_ = v_isSharedCheck_783_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_snapshotTasks_769_);
lean_inc(v_infoState_768_);
lean_inc(v_messages_767_);
lean_inc(v_cache_766_);
lean_inc(v_traceState_765_);
lean_inc(v_auxDeclNGen_764_);
lean_inc(v_ngen_763_);
lean_inc(v_nextMacroScope_762_);
lean_inc(v_env_761_);
lean_dec(v___x_758_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_783_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_inc(v_openDecls_760_);
lean_inc(v_currNamespace_759_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_currNamespace_759_);
lean_ctor_set(v___x_773_, 1, v_openDecls_760_);
v___x_774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___y_750_);
lean_inc_ref(v___y_752_);
lean_inc_ref(v___y_749_);
v___x_775_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_775_, 0, v___y_749_);
lean_ctor_set(v___x_775_, 1, v___y_753_);
lean_ctor_set(v___x_775_, 2, v___y_755_);
lean_ctor_set(v___x_775_, 3, v___y_752_);
lean_ctor_set(v___x_775_, 4, v___x_774_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*5, v___y_751_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*5 + 1, v___y_754_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*5 + 2, v_isSilent_742_);
v___x_776_ = l_Lean_MessageLog_add(v___x_775_, v_messages_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 6, v___x_776_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_env_761_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_nextMacroScope_762_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_ngen_763_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_auxDeclNGen_764_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_traceState_765_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_cache_766_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_infoState_768_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_snapshotTasks_769_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_st_ref_set(v___y_757_, v___x_778_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
}
v___jp_784_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_808_; 
v___x_793_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_740_);
v___x_794_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v___x_793_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_808_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_808_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_808_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc_ref_n(v___y_788_, 2);
v___x_799_ = l_Lean_FileMap_toPosition(v___y_788_, v___y_789_);
lean_dec(v___y_789_);
v___x_800_ = l_Lean_FileMap_toPosition(v___y_788_, v___y_792_);
lean_dec(v___y_792_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0));
if (v___y_786_ == 0)
{
lean_del_object(v___x_797_);
lean_dec_ref(v___y_785_);
v___y_749_ = v___y_787_;
v___y_750_ = v_a_795_;
v___y_751_ = v___y_790_;
v___y_752_ = v___x_802_;
v___y_753_ = v___x_799_;
v___y_754_ = v___y_791_;
v___y_755_ = v___x_801_;
v___y_756_ = v___y_745_;
v___y_757_ = v___y_746_;
goto v___jp_748_;
}
else
{
uint8_t v___x_803_; 
lean_inc(v_a_795_);
v___x_803_ = l_Lean_MessageData_hasTag(v___y_785_, v_a_795_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec_ref_known(v___x_801_, 1);
lean_dec_ref(v___x_799_);
lean_dec(v_a_795_);
v___x_804_ = lean_box(0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
lean_del_object(v___x_797_);
v___y_749_ = v___y_787_;
v___y_750_ = v_a_795_;
v___y_751_ = v___y_790_;
v___y_752_ = v___x_802_;
v___y_753_ = v___x_799_;
v___y_754_ = v___y_791_;
v___y_755_ = v___x_801_;
v___y_756_ = v___y_745_;
v___y_757_ = v___y_746_;
goto v___jp_748_;
}
}
}
}
v___jp_809_:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Syntax_getTailPos_x3f(v___y_811_, v___y_815_);
lean_dec(v___y_811_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_inc(v___y_817_);
v___y_785_ = v___y_810_;
v___y_786_ = v___y_812_;
v___y_787_ = v___y_814_;
v___y_788_ = v___y_813_;
v___y_789_ = v___y_817_;
v___y_790_ = v___y_815_;
v___y_791_ = v___y_816_;
v___y_792_ = v___y_817_;
goto v___jp_784_;
}
else
{
lean_object* v_val_819_; 
v_val_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___x_818_, 1);
v___y_785_ = v___y_810_;
v___y_786_ = v___y_812_;
v___y_787_ = v___y_814_;
v___y_788_ = v___y_813_;
v___y_789_ = v___y_817_;
v___y_790_ = v___y_815_;
v___y_791_ = v___y_816_;
v___y_792_ = v_val_819_;
goto v___jp_784_;
}
}
v___jp_820_:
{
lean_object* v_ref_828_; lean_object* v___x_829_; 
v_ref_828_ = l_Lean_replaceRef(v_ref_739_, v___y_826_);
v___x_829_ = l_Lean_Syntax_getPos_x3f(v_ref_828_, v___y_825_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___y_810_ = v___y_821_;
v___y_811_ = v_ref_828_;
v___y_812_ = v___y_822_;
v___y_813_ = v___y_824_;
v___y_814_ = v___y_823_;
v___y_815_ = v___y_825_;
v___y_816_ = v___y_827_;
v___y_817_ = v___x_830_;
goto v___jp_809_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_829_, 1);
v___y_810_ = v___y_821_;
v___y_811_ = v_ref_828_;
v___y_812_ = v___y_822_;
v___y_813_ = v___y_824_;
v___y_814_ = v___y_823_;
v___y_815_ = v___y_825_;
v___y_816_ = v___y_827_;
v___y_817_ = v_val_831_;
goto v___jp_809_;
}
}
v___jp_833_:
{
if (v___y_840_ == 0)
{
v___y_821_ = v___y_838_;
v___y_822_ = v___y_834_;
v___y_823_ = v___y_836_;
v___y_824_ = v___y_835_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_837_;
v___y_827_ = v_severity_741_;
goto v___jp_820_;
}
else
{
v___y_821_ = v___y_838_;
v___y_822_ = v___y_834_;
v___y_823_ = v___y_836_;
v___y_824_ = v___y_835_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_837_;
v___y_827_ = v___x_832_;
goto v___jp_820_;
}
}
v___jp_841_:
{
if (v___y_842_ == 0)
{
lean_object* v_fileName_843_; lean_object* v_fileMap_844_; lean_object* v_options_845_; lean_object* v_ref_846_; uint8_t v_suppressElabErrors_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___f_850_; uint8_t v___x_851_; uint8_t v___x_852_; 
v_fileName_843_ = lean_ctor_get(v___y_745_, 0);
v_fileMap_844_ = lean_ctor_get(v___y_745_, 1);
v_options_845_ = lean_ctor_get(v___y_745_, 2);
v_ref_846_ = lean_ctor_get(v___y_745_, 5);
v_suppressElabErrors_847_ = lean_ctor_get_uint8(v___y_745_, sizeof(void*)*14 + 1);
v___x_848_ = lean_box(v___y_842_);
v___x_849_ = lean_box(v_suppressElabErrors_847_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_850_, 0, v___x_848_);
lean_closure_set(v___f_850_, 1, v___x_849_);
v___x_851_ = 1;
v___x_852_ = l_Lean_instBEqMessageSeverity_beq(v_severity_741_, v___x_851_);
if (v___x_852_ == 0)
{
v___y_834_ = v_suppressElabErrors_847_;
v___y_835_ = v_fileMap_844_;
v___y_836_ = v_fileName_843_;
v___y_837_ = v_ref_846_;
v___y_838_ = v___f_850_;
v___y_839_ = v___y_842_;
v___y_840_ = v___x_852_;
goto v___jp_833_;
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = l_Lean_warningAsError;
v___x_854_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_options_845_, v___x_853_);
v___y_834_ = v_suppressElabErrors_847_;
v___y_835_ = v_fileMap_844_;
v___y_836_ = v_fileName_843_;
v___y_837_ = v_ref_846_;
v___y_838_ = v___f_850_;
v___y_839_ = v___y_842_;
v___y_840_ = v___x_854_;
goto v___jp_833_;
}
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref(v_msgData_740_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___boxed(lean_object* v_ref_859_, lean_object* v_msgData_860_, lean_object* v_severity_861_, lean_object* v_isSilent_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v_severity_boxed_868_; uint8_t v_isSilent_boxed_869_; lean_object* v_res_870_; 
v_severity_boxed_868_ = lean_unbox(v_severity_861_);
v_isSilent_boxed_869_ = lean_unbox(v_isSilent_862_);
v_res_870_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_859_, v_msgData_860_, v_severity_boxed_868_, v_isSilent_boxed_869_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v_ref_859_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(lean_object* v_ref_871_, lean_object* v_msgData_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; 
v___x_880_ = 0;
v___x_881_ = 0;
v___x_882_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_871_, v_msgData_872_, v___x_880_, v___x_881_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4___boxed(lean_object* v_ref_883_, lean_object* v_msgData_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(v_ref_883_, v_msgData_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v_ref_883_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(lean_object* v_msgData_893_, lean_object* v_macroStack_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_options_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_options_897_ = lean_ctor_get(v___y_895_, 2);
v___x_898_ = l_Lean_Elab_pp_macroStack;
v___x_899_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_options_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_macroStack_894_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v_msgData_893_);
return v___x_900_;
}
else
{
if (lean_obj_tag(v_macroStack_894_) == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_msgData_893_);
return v___x_901_;
}
else
{
lean_object* v_head_902_; lean_object* v_after_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_918_; 
v_head_902_ = lean_ctor_get(v_macroStack_894_, 0);
lean_inc(v_head_902_);
v_after_903_ = lean_ctor_get(v_head_902_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_head_902_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_head_902_, 0);
lean_dec(v_unused_919_);
v___x_905_ = v_head_902_;
v_isShared_906_ = v_isSharedCheck_918_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_after_903_);
lean_dec(v_head_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_918_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 7);
lean_ctor_set(v___x_905_, 1, v___x_907_);
lean_ctor_set(v___x_905_, 0, v_msgData_893_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_msgData_893_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_917_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_msgData_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_910_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_MessageData_ofSyntax(v_after_903_);
v___x_913_ = l_Lean_indentD(v___x_912_);
v_msgData_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_914_, 0, v___x_911_);
lean_ctor_set(v_msgData_914_, 1, v___x_913_);
v___x_915_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(v_msgData_914_, v_macroStack_894_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_msgData_920_, lean_object* v_macroStack_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_920_, v_macroStack_921_, v___y_922_);
lean_dec_ref(v___y_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_ref_933_; lean_object* v___x_934_; lean_object* v_a_935_; lean_object* v_macroStack_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_ref_933_ = lean_ctor_get(v___y_930_, 5);
v___x_934_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msg_925_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_934_);
v_macroStack_936_ = lean_ctor_get(v___y_926_, 1);
v___x_937_ = l_Lean_Elab_getBetterRef(v_ref_933_, v_macroStack_936_);
lean_inc(v_macroStack_936_);
v___x_938_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_a_935_, v_macroStack_936_, v___y_930_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_937_);
lean_ctor_set(v___x_943_, 1, v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 1);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg___boxed(lean_object* v_msg_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(lean_object* v_ref_957_, lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_fileName_966_; lean_object* v_fileMap_967_; lean_object* v_options_968_; lean_object* v_currRecDepth_969_; lean_object* v_maxRecDepth_970_; lean_object* v_ref_971_; lean_object* v_currNamespace_972_; lean_object* v_openDecls_973_; lean_object* v_initHeartbeats_974_; lean_object* v_maxHeartbeats_975_; lean_object* v_quotContext_976_; lean_object* v_currMacroScope_977_; uint8_t v_diag_978_; lean_object* v_cancelTk_x3f_979_; uint8_t v_suppressElabErrors_980_; lean_object* v_inheritedTraceOptions_981_; lean_object* v_ref_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_fileName_966_ = lean_ctor_get(v___y_963_, 0);
v_fileMap_967_ = lean_ctor_get(v___y_963_, 1);
v_options_968_ = lean_ctor_get(v___y_963_, 2);
v_currRecDepth_969_ = lean_ctor_get(v___y_963_, 3);
v_maxRecDepth_970_ = lean_ctor_get(v___y_963_, 4);
v_ref_971_ = lean_ctor_get(v___y_963_, 5);
v_currNamespace_972_ = lean_ctor_get(v___y_963_, 6);
v_openDecls_973_ = lean_ctor_get(v___y_963_, 7);
v_initHeartbeats_974_ = lean_ctor_get(v___y_963_, 8);
v_maxHeartbeats_975_ = lean_ctor_get(v___y_963_, 9);
v_quotContext_976_ = lean_ctor_get(v___y_963_, 10);
v_currMacroScope_977_ = lean_ctor_get(v___y_963_, 11);
v_diag_978_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*14);
v_cancelTk_x3f_979_ = lean_ctor_get(v___y_963_, 12);
v_suppressElabErrors_980_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_981_ = lean_ctor_get(v___y_963_, 13);
v_ref_982_ = l_Lean_replaceRef(v_ref_957_, v_ref_971_);
lean_inc_ref(v_inheritedTraceOptions_981_);
lean_inc(v_cancelTk_x3f_979_);
lean_inc(v_currMacroScope_977_);
lean_inc(v_quotContext_976_);
lean_inc(v_maxHeartbeats_975_);
lean_inc(v_initHeartbeats_974_);
lean_inc(v_openDecls_973_);
lean_inc(v_currNamespace_972_);
lean_inc(v_maxRecDepth_970_);
lean_inc(v_currRecDepth_969_);
lean_inc_ref(v_options_968_);
lean_inc_ref(v_fileMap_967_);
lean_inc_ref(v_fileName_966_);
v___x_983_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_983_, 0, v_fileName_966_);
lean_ctor_set(v___x_983_, 1, v_fileMap_967_);
lean_ctor_set(v___x_983_, 2, v_options_968_);
lean_ctor_set(v___x_983_, 3, v_currRecDepth_969_);
lean_ctor_set(v___x_983_, 4, v_maxRecDepth_970_);
lean_ctor_set(v___x_983_, 5, v_ref_982_);
lean_ctor_set(v___x_983_, 6, v_currNamespace_972_);
lean_ctor_set(v___x_983_, 7, v_openDecls_973_);
lean_ctor_set(v___x_983_, 8, v_initHeartbeats_974_);
lean_ctor_set(v___x_983_, 9, v_maxHeartbeats_975_);
lean_ctor_set(v___x_983_, 10, v_quotContext_976_);
lean_ctor_set(v___x_983_, 11, v_currMacroScope_977_);
lean_ctor_set(v___x_983_, 12, v_cancelTk_x3f_979_);
lean_ctor_set(v___x_983_, 13, v_inheritedTraceOptions_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*14, v_diag_978_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*14 + 1, v_suppressElabErrors_980_);
v___x_984_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___x_983_, v___y_964_);
lean_dec_ref_known(v___x_983_, 14);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg___boxed(lean_object* v_ref_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_ref_985_, v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v_ref_985_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(lean_object* v_msg_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0));
v___x_997_ = lean_panic_fn_borrowed(v___x_996_, v_msg_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(lean_object* v_val_998_, lean_object* v___x_999_, lean_object* v_a_x3f_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_get_set_stderr(v_val_998_);
lean_dec_ref(v___x_1002_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_999_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_val_1004_, lean_object* v___x_1005_, lean_object* v_a_x3f_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v_val_1004_, v___x_1005_, v_a_x3f_1006_);
lean_dec(v_a_x3f_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(lean_object* v_h_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_r_1020_; 
v___x_1018_ = lean_get_set_stderr(v_h_1009_);
v___x_1019_ = lean_box(0);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
v_r_1020_ = lean_apply_7(v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, lean_box(0));
if (lean_obj_tag(v_r_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1037_; 
v_a_1021_ = lean_ctor_get(v_r_1020_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_r_1020_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1023_ = v_r_1020_;
v_isShared_1024_ = v_isSharedCheck_1037_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v_r_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1037_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
lean_inc(v_a_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v___x_1027_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v___x_1018_, v___x_1019_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1035_);
v___x_1029_ = v___x_1027_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v___x_1027_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_a_1021_);
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1021_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1038_ = lean_ctor_get(v_r_1020_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_r_1020_, 1);
v___x_1039_ = lean_box(0);
v___x_1040_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v___x_1018_, v___x_1019_, v___x_1039_);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v___x_1040_, 0);
lean_dec(v_unused_1048_);
v___x_1042_ = v___x_1040_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v___x_1040_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 1);
lean_ctor_set(v___x_1042_, 0, v_a_1038_);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1038_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___boxed(lean_object* v_h_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_1049_, v_x_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(lean_object* v_00_u03b1_1059_, lean_object* v_h_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_1060_, v_x_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_h_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(v_00_u03b1_1070_, v_h_1071_, v_x_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(lean_object* v_val_1081_, lean_object* v___x_1082_, lean_object* v_a_x3f_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_get_set_stdin(v_val_1081_);
lean_dec_ref(v___x_1085_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1082_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_val_1087_, lean_object* v___x_1088_, lean_object* v_a_x3f_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v_val_1087_, v___x_1088_, v_a_x3f_1089_);
lean_dec(v_a_x3f_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(lean_object* v_h_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_r_1103_; 
v___x_1101_ = lean_get_set_stdin(v_h_1092_);
v___x_1102_ = lean_box(0);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
v_r_1103_ = lean_apply_7(v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
if (lean_obj_tag(v_r_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1120_; 
v_a_1104_ = lean_ctor_get(v_r_1103_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_r_1103_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1106_ = v_r_1103_;
v_isShared_1107_ = v_isSharedCheck_1120_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v_r_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1120_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
lean_inc(v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 1);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v___x_1110_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v___x_1101_, v___x_1102_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1110_, 0);
lean_dec(v_unused_1118_);
v___x_1112_ = v___x_1110_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v___x_1110_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_a_1104_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1104_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1121_ = lean_ctor_get(v_r_1103_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v_r_1103_, 1);
v___x_1122_ = lean_box(0);
v___x_1123_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v___x_1101_, v___x_1102_, v___x_1122_);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1131_);
v___x_1125_ = v___x_1123_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v___x_1123_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 1);
lean_ctor_set(v___x_1125_, 0, v_a_1121_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1121_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___boxed(lean_object* v_h_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_1132_, v_x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(lean_object* v_val_1142_, lean_object* v___x_1143_, lean_object* v_a_x3f_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_get_set_stdout(v_val_1142_);
lean_dec_ref(v___x_1146_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1143_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_val_1148_, lean_object* v___x_1149_, lean_object* v_a_x3f_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v_val_1148_, v___x_1149_, v_a_x3f_1150_);
lean_dec(v_a_x3f_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(lean_object* v_h_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_r_1164_; 
v___x_1162_ = lean_get_set_stdout(v_h_1153_);
v___x_1163_ = lean_box(0);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
v_r_1164_ = lean_apply_7(v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, lean_box(0));
if (lean_obj_tag(v_r_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1181_; 
v_a_1165_ = lean_ctor_get(v_r_1164_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_r_1164_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1167_ = v_r_1164_;
v_isShared_1168_ = v_isSharedCheck_1181_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v_r_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1181_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
lean_inc(v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 1);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v___x_1171_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v___x_1162_, v___x_1163_, v___x_1170_);
lean_dec_ref(v___x_1170_);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v___x_1171_, 0);
lean_dec(v_unused_1179_);
v___x_1173_ = v___x_1171_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_dec(v___x_1171_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_a_1165_);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1165_);
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
else
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_a_1182_ = lean_ctor_get(v_r_1164_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v_r_1164_, 1);
v___x_1183_ = lean_box(0);
v___x_1184_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v___x_1162_, v___x_1163_, v___x_1183_);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v___x_1184_, 0);
lean_dec(v_unused_1192_);
v___x_1186_ = v___x_1184_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v___x_1184_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 1);
lean_ctor_set(v___x_1186_, 0, v_a_1182_);
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1182_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___boxed(lean_object* v_h_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_1193_, v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(lean_object* v_00_u03b1_1203_, lean_object* v_h_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_1204_, v_x_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_h_1215_, lean_object* v_x_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(v_00_u03b1_1214_, v_h_1215_, v_x_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1224_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = l_ByteArray_empty;
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1231_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3));
v___x_1232_ = lean_unsigned_to_nat(46u);
v___x_1233_ = lean_unsigned_to_nat(193u);
v___x_1234_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2));
v___x_1235_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1));
v___x_1236_ = l_mkPanicMessageWithDecl(v___x_1235_, v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(lean_object* v_x_1237_, uint8_t v_isolateStderr_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___y_1257_; 
v___x_1251_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0);
v___x_1252_ = lean_st_mk_ref(v___x_1251_);
v___x_1253_ = lean_st_mk_ref(v___x_1251_);
v___x_1254_ = l_IO_FS_Stream_ofBuffer(v___x_1252_);
lean_inc(v___x_1253_);
v___x_1255_ = l_IO_FS_Stream_ofBuffer(v___x_1253_);
if (v_isolateStderr_1238_ == 0)
{
v___y_1257_ = v_x_1237_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1275_; 
lean_inc_ref(v___x_1255_);
v___x_1275_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed), 10, 3);
lean_closure_set(v___x_1275_, 0, lean_box(0));
lean_closure_set(v___x_1275_, 1, v___x_1255_);
lean_closure_set(v___x_1275_, 2, v_x_1237_);
v___y_1257_ = v___x_1275_;
goto v___jp_1256_;
}
v___jp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___y_1248_);
lean_ctor_set(v___x_1249_, 1, v___y_1247_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed), 10, 3);
lean_closure_set(v___x_1258_, 0, lean_box(0));
lean_closure_set(v___x_1258_, 1, v___x_1255_);
lean_closure_set(v___x_1258_, 2, v___y_1257_);
v___x_1259_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v___x_1254_, v___x_1258_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v_data_1262_; uint8_t v___x_1263_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = lean_st_ref_get(v___x_1253_);
lean_dec(v___x_1253_);
v_data_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_ref(v_data_1262_);
lean_dec(v___x_1261_);
v___x_1263_ = lean_string_validate_utf8(v_data_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref(v_data_1262_);
v___x_1264_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4);
v___x_1265_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(v___x_1264_);
v___y_1247_ = v_a_1260_;
v___y_1248_ = v___x_1265_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_string_from_utf8_unchecked(v_data_1262_);
v___y_1247_ = v_a_1260_;
v___y_1248_ = v___x_1266_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v___x_1253_);
v_a_1267_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1259_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1259_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___boxed(lean_object* v_x_1276_, lean_object* v_isolateStderr_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_isolateStderr_boxed_1285_; lean_object* v_res_1286_; 
v_isolateStderr_boxed_1285_ = lean_unbox(v_isolateStderr_1277_);
v_res_1286_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_1276_, v_isolateStderr_boxed_1285_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1286_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Lean_Level_succ___override(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2);
v___x_1295_ = l_Lean_mkSort(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(lean_object* v_stx_1311_, lean_object* v_expectedType_x3f_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1));
lean_inc(v_stx_1311_);
v___x_1321_ = l_Lean_Syntax_isOfKind(v_stx_1311_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_expectedType_x3f_1312_);
lean_dec(v_stx_1311_);
v___x_1322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
return v___x_1322_;
}
else
{
lean_object* v_fileName_1323_; lean_object* v_fileMap_1324_; lean_object* v_options_1325_; lean_object* v_currRecDepth_1326_; lean_object* v_maxRecDepth_1327_; lean_object* v_ref_1328_; lean_object* v_currNamespace_1329_; lean_object* v_openDecls_1330_; lean_object* v_initHeartbeats_1331_; lean_object* v_maxHeartbeats_1332_; lean_object* v_quotContext_1333_; lean_object* v_currMacroScope_1334_; uint8_t v_diag_1335_; lean_object* v_cancelTk_x3f_1336_; uint8_t v_suppressElabErrors_1337_; lean_object* v_inheritedTraceOptions_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v_ref_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_fileName_1323_ = lean_ctor_get(v_a_1317_, 0);
v_fileMap_1324_ = lean_ctor_get(v_a_1317_, 1);
v_options_1325_ = lean_ctor_get(v_a_1317_, 2);
v_currRecDepth_1326_ = lean_ctor_get(v_a_1317_, 3);
v_maxRecDepth_1327_ = lean_ctor_get(v_a_1317_, 4);
v_ref_1328_ = lean_ctor_get(v_a_1317_, 5);
v_currNamespace_1329_ = lean_ctor_get(v_a_1317_, 6);
v_openDecls_1330_ = lean_ctor_get(v_a_1317_, 7);
v_initHeartbeats_1331_ = lean_ctor_get(v_a_1317_, 8);
v_maxHeartbeats_1332_ = lean_ctor_get(v_a_1317_, 9);
v_quotContext_1333_ = lean_ctor_get(v_a_1317_, 10);
v_currMacroScope_1334_ = lean_ctor_get(v_a_1317_, 11);
v_diag_1335_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*14);
v_cancelTk_x3f_1336_ = lean_ctor_get(v_a_1317_, 12);
v_suppressElabErrors_1337_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1338_ = lean_ctor_get(v_a_1317_, 13);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = l_Lean_Syntax_getArg(v_stx_1311_, v___x_1339_);
v___x_1341_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4);
v___x_1342_ = 0;
v___x_1343_ = lean_box(0);
v_ref_1344_ = l_Lean_replaceRef(v___x_1340_, v_ref_1328_);
lean_inc_ref(v_inheritedTraceOptions_1338_);
lean_inc(v_cancelTk_x3f_1336_);
lean_inc(v_currMacroScope_1334_);
lean_inc(v_quotContext_1333_);
lean_inc(v_maxHeartbeats_1332_);
lean_inc(v_initHeartbeats_1331_);
lean_inc(v_openDecls_1330_);
lean_inc(v_currNamespace_1329_);
lean_inc(v_ref_1344_);
lean_inc(v_maxRecDepth_1327_);
lean_inc(v_currRecDepth_1326_);
lean_inc_ref(v_options_1325_);
lean_inc_ref(v_fileMap_1324_);
lean_inc_ref(v_fileName_1323_);
v___x_1345_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1345_, 0, v_fileName_1323_);
lean_ctor_set(v___x_1345_, 1, v_fileMap_1324_);
lean_ctor_set(v___x_1345_, 2, v_options_1325_);
lean_ctor_set(v___x_1345_, 3, v_currRecDepth_1326_);
lean_ctor_set(v___x_1345_, 4, v_maxRecDepth_1327_);
lean_ctor_set(v___x_1345_, 5, v_ref_1344_);
lean_ctor_set(v___x_1345_, 6, v_currNamespace_1329_);
lean_ctor_set(v___x_1345_, 7, v_openDecls_1330_);
lean_ctor_set(v___x_1345_, 8, v_initHeartbeats_1331_);
lean_ctor_set(v___x_1345_, 9, v_maxHeartbeats_1332_);
lean_ctor_set(v___x_1345_, 10, v_quotContext_1333_);
lean_ctor_set(v___x_1345_, 11, v_currMacroScope_1334_);
lean_ctor_set(v___x_1345_, 12, v_cancelTk_x3f_1336_);
lean_ctor_set(v___x_1345_, 13, v_inheritedTraceOptions_1338_);
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*14, v_diag_1335_);
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*14 + 1, v_suppressElabErrors_1337_);
v___x_1346_ = l_Lean_Meta_mkFreshExprMVar(v___x_1341_, v___x_1342_, v___x_1343_, v_a_1315_, v_a_1316_, v___x_1345_, v_a_1318_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1489_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1489_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1489_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v_tk_1352_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___x_1376_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1435_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v_tk_1352_ = l_Lean_Syntax_getArg(v_stx_1311_, v___x_1351_);
lean_dec(v_stx_1311_);
v___x_1376_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2);
if (lean_obj_tag(v_expectedType_x3f_1312_) == 0)
{
v___y_1435_ = v_a_1347_;
goto v___jp_1434_;
}
else
{
lean_object* v_val_1488_; 
lean_dec(v_a_1347_);
v_val_1488_ = lean_ctor_get(v_expectedType_x3f_1312_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v_expectedType_x3f_1312_, 1);
v___y_1435_ = v_val_1488_;
goto v___jp_1434_;
}
v___jp_1353_:
{
if (lean_obj_tag(v___y_1354_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1371_; 
lean_del_object(v___x_1349_);
v_a_1361_ = lean_ctor_get(v___y_1354_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___y_1354_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1363_ = v___y_1354_;
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___y_1354_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_io_error_to_string(v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 3);
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = l_Lean_MessageData_ofFormat(v___x_1367_);
v___x_1369_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_tk_1352_, v___x_1368_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_tk_1352_);
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; 
lean_dec_ref(v___y_1359_);
lean_dec(v_tk_1352_);
v_a_1372_ = lean_ctor_get(v___y_1354_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___y_1354_, 1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_a_1372_);
v___x_1374_ = v___x_1349_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
v___jp_1377_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1385_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8));
v___x_1386_ = lean_mk_empty_array_with_capacity(v___x_1339_);
v___x_1387_ = lean_array_push(v___x_1386_, v___y_1378_);
v___x_1388_ = l_Lean_Meta_mkAppM(v___x_1385_, v___x_1387_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1433_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1433_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1433_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7);
v___x_1394_ = 1;
v___x_1395_ = l_Lean_Meta_evalExpr___redArg(v___x_1393_, v_a_1389_, v___x_1394_, v___x_1321_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___f_1397_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1397_, 0, v_a_1396_);
v___x_1398_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v___f_1397_, v___x_1321_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v_fst_1400_ = lean_ctor_get(v_a_1399_, 0);
lean_inc(v_fst_1400_);
v_snd_1401_ = lean_ctor_get(v_a_1399_, 1);
lean_inc(v_snd_1401_);
lean_dec(v_a_1399_);
v___x_1402_ = lean_string_utf8_byte_size(v_fst_1400_);
v___x_1403_ = lean_nat_dec_eq(v___x_1402_, v___x_1351_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1405_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 3);
lean_ctor_set(v___x_1391_, 0, v_fst_1400_);
v___x_1405_ = v___x_1391_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_fst_1400_);
v___x_1405_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = l_Lean_MessageData_ofFormat(v___x_1405_);
v___x_1407_ = l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(v_tk_1352_, v___x_1406_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_dec_ref_known(v___x_1407_, 1);
v___y_1354_ = v_snd_1401_;
v___y_1355_ = v___y_1379_;
v___y_1356_ = v___y_1380_;
v___y_1357_ = v___y_1381_;
v___y_1358_ = v___y_1382_;
v___y_1359_ = v___y_1383_;
v___y_1360_ = v___y_1384_;
goto v___jp_1353_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_snd_1401_);
lean_dec_ref(v___y_1383_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_dec(v_fst_1400_);
lean_del_object(v___x_1391_);
v___y_1354_ = v_snd_1401_;
v___y_1355_ = v___y_1379_;
v___y_1356_ = v___y_1380_;
v___y_1357_ = v___y_1381_;
v___y_1358_ = v___y_1382_;
v___y_1359_ = v___y_1383_;
v___y_1360_ = v___y_1384_;
goto v___jp_1353_;
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1391_);
lean_dec_ref(v___y_1383_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
v_a_1417_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1398_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1398_);
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
lean_del_object(v___x_1391_);
lean_dec_ref(v___y_1383_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
v_a_1425_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1395_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1395_);
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
}
else
{
lean_dec_ref(v___y_1383_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
return v___x_1388_;
}
}
v___jp_1434_:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1436_ = l_Lean_Expr_app___override(v___x_1376_, v___y_1435_);
v___x_1437_ = 0;
v___x_1438_ = l_Lean_SourceInfo_fromRef(v_ref_1344_, v___x_1437_);
lean_dec(v_ref_1344_);
v___x_1439_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9));
v___x_1440_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10));
lean_inc(v___x_1438_);
v___x_1441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1438_);
lean_ctor_set(v___x_1441_, 1, v___x_1439_);
v___x_1442_ = l_Lean_Syntax_node2(v___x_1438_, v___x_1440_, v___x_1441_, v___x_1340_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1436_);
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1442_, v___x_1443_, v___x_1321_, v___x_1321_, v___x_1444_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v___x_1345_, v_a_1318_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1437_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v___x_1345_, v_a_1318_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1450_; 
lean_dec_ref_known(v___x_1447_, 1);
v___x_1448_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_a_1446_, v_a_1316_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_n(v_a_1449_, 2);
lean_dec_ref(v___x_1448_);
v___x_1450_ = l_Lean_Meta_getMVars(v_a_1449_, v_a_1315_, v_a_1316_, v___x_1345_, v_a_1318_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1451_, v___x_1444_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v___x_1345_, v_a_1318_);
lean_dec(v_a_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; uint8_t v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1452_, 1);
v___x_1454_ = lean_unbox(v_a_1453_);
lean_dec(v_a_1453_);
if (v___x_1454_ == 0)
{
v___y_1378_ = v_a_1449_;
v___y_1379_ = v_a_1313_;
v___y_1380_ = v_a_1314_;
v___y_1381_ = v_a_1315_;
v___y_1382_ = v_a_1316_;
v___y_1383_ = v___x_1345_;
v___y_1384_ = v_a_1318_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1455_; lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1449_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
lean_dec_ref_known(v___x_1345_, 14);
v___x_1455_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
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
lean_dec(v_a_1449_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
lean_dec_ref_known(v___x_1345_, 14);
v_a_1464_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1452_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1452_);
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
lean_dec(v_a_1449_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
lean_dec_ref_known(v___x_1345_, 14);
v_a_1472_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1450_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1450_);
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
lean_dec(v_a_1446_);
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
lean_dec_ref_known(v___x_1345_, 14);
v_a_1480_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1447_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1447_);
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
lean_dec(v_tk_1352_);
lean_del_object(v___x_1349_);
lean_dec_ref_known(v___x_1345_, 14);
return v___x_1445_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1345_, 14);
lean_dec(v_ref_1344_);
lean_dec(v___x_1340_);
lean_dec(v_expectedType_x3f_1312_);
lean_dec(v_stx_1311_);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed(lean_object* v_stx_1490_, lean_object* v_expectedType_x3f_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(v_stx_1490_, v_expectedType_x3f_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(lean_object* v_00_u03b1_1500_, lean_object* v_h_1501_, lean_object* v_x_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_1501_, v_x_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_h_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(v_00_u03b1_1511_, v_h_1512_, v_x_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(lean_object* v_00_u03b1_1522_, lean_object* v_x_1523_, uint8_t v_isolateStderr_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_1523_, v_isolateStderr_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___boxed(lean_object* v_00_u03b1_1533_, lean_object* v_x_1534_, lean_object* v_isolateStderr_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v_isolateStderr_boxed_1543_; lean_object* v_res_1544_; 
v_isolateStderr_boxed_1543_ = lean_unbox(v_isolateStderr_1535_);
v_res_1544_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(v_00_u03b1_1533_, v_x_1534_, v_isolateStderr_boxed_1543_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(lean_object* v_00_u03b1_1545_, lean_object* v_ref_1546_, lean_object* v_msg_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_ref_1546_, v_msg_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___boxed(lean_object* v_00_u03b1_1556_, lean_object* v_ref_1557_, lean_object* v_msg_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(v_00_u03b1_1556_, v_ref_1557_, v_msg_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v_ref_1557_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(lean_object* v_00_u03b1_1567_, lean_object* v_msg_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_msg_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(v_00_u03b1_1577_, v_msg_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(lean_object* v_ref_1587_, lean_object* v_msgData_1588_, uint8_t v_severity_1589_, uint8_t v_isSilent_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_1587_, v_msgData_1588_, v_severity_1589_, v_isSilent_1590_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___boxed(lean_object* v_ref_1599_, lean_object* v_msgData_1600_, lean_object* v_severity_1601_, lean_object* v_isSilent_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v_severity_boxed_1610_; uint8_t v_isSilent_boxed_1611_; lean_object* v_res_1612_; 
v_severity_boxed_1610_ = lean_unbox(v_severity_1601_);
v_isSilent_boxed_1611_ = lean_unbox(v_isSilent_1602_);
v_res_1612_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(v_ref_1599_, v_msgData_1600_, v_severity_boxed_1610_, v_isSilent_boxed_1611_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v_ref_1599_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(lean_object* v_msgData_1613_, lean_object* v_macroStack_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_1613_, v_macroStack_1614_, v___y_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___boxed(lean_object* v_msgData_1623_, lean_object* v_macroStack_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(v_msgData_1623_, v_macroStack_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1(){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1638_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1639_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1));
v___x_1640_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1));
v___x_1641_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed), 9, 0);
v___x_1642_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1638_, v___x_1639_, v___x_1640_, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___boxed(lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
return v_res_1644_;
}
}
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
