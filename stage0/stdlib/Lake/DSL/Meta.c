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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5;
static lean_once_cell_t l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toExprIO"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__7_value),LEAN_SCALAR_PTR_LITERAL(100, 226, 78, 143, 214, 112, 160, 165)}};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9 = (const lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10_value_aux_1),((lean_object*)&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(lean_object* v_c_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2);
v___x_42_ = 0;
v___x_43_ = l_Lean_Elab_Term_evalTerm___redArg(v___x_41_, v_c_33_, v___x_42_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
return v___x_43_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_33_ = stack[0].m_obj;
lean_object* v_a_34_ = stack[1].m_obj;
lean_object* v_a_35_ = stack[2].m_obj;
lean_object* v_a_36_ = stack[3].m_obj;
lean_object* v_a_37_ = stack[4].m_obj;
lean_object* v_a_38_ = stack[5].m_obj;
lean_object* v_a_39_ = stack[6].m_obj;
lean_object* v_res_44_;
v_res_44_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(v_c_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___boxed(lean_object* v_c_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1(v_c_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_53_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(lean_object* v___x_54_, lean_object* v_x_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_unsafe__1___closed__2);
v___x_64_ = 0;
v___x_65_ = l_Lean_Elab_Term_evalTerm___redArg(v___x_63_, v___x_54_, v___x_64_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
return v___x_65_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_54_ = stack[0].m_obj;
lean_object* v_x_55_ = stack[1].m_obj;
lean_object* v___y_56_ = stack[2].m_obj;
lean_object* v___y_57_ = stack[3].m_obj;
lean_object* v___y_58_ = stack[4].m_obj;
lean_object* v___y_59_ = stack[5].m_obj;
lean_object* v___y_60_ = stack[6].m_obj;
lean_object* v___y_61_ = stack[7].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(v___x_54_, v_x_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed(lean_object* v___x_67_, lean_object* v_x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0(v___x_67_, v_x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec_ref(v_x_68_);
return v_res_76_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_box(1);
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_83_ = l_Lean_MessageData_ofFormat(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
return v_x_84_;
}
else
{
lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_109_; 
v_head_86_ = lean_ctor_get(v_x_85_, 0);
v_tail_87_ = lean_ctor_get(v_x_85_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_109_ == 0)
{
v___x_89_ = v_x_85_;
v_isShared_90_ = v_isSharedCheck_109_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_head_86_);
lean_dec(v_x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_109_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_before_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_107_; 
v_before_91_ = lean_ctor_get(v_head_86_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_head_86_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_head_86_, 1);
lean_dec(v_unused_108_);
v___x_93_ = v_head_86_;
v_isShared_94_ = v_isSharedCheck_107_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_before_91_);
lean_dec(v_head_86_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_107_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 7);
lean_ctor_set(v___x_93_, 1, v___x_95_);
lean_ctor_set(v___x_93_, 0, v_x_84_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_x_84_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_106_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__3);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 7);
lean_ctor_set(v___x_89_, 1, v___x_98_);
lean_ctor_set(v___x_89_, 0, v___x_97_);
v___x_100_ = v___x_89_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = l_Lean_MessageData_ofSyntax(v_before_91_);
v___x_102_ = l_Lean_indentD(v___x_101_);
v___x_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_100_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v_x_84_ = v___x_103_;
v_x_85_ = v_tail_87_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(lean_object* v_opts_110_, lean_object* v_opt_111_){
_start:
{
lean_object* v_name_112_; lean_object* v_defValue_113_; lean_object* v_map_114_; lean_object* v___x_115_; 
v_name_112_ = lean_ctor_get(v_opt_111_, 0);
v_defValue_113_ = lean_ctor_get(v_opt_111_, 1);
v_map_114_ = lean_ctor_get(v_opts_110_, 0);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_114_, v_name_112_);
if (lean_obj_tag(v___x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = lean_unbox(v_defValue_113_);
return v___x_116_;
}
else
{
lean_object* v_val_117_; 
v_val_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v___x_115_, 1);
if (lean_obj_tag(v_val_117_) == 1)
{
uint8_t v_v_118_; 
v_v_118_ = lean_ctor_get_uint8(v_val_117_, 0);
lean_dec_ref_known(v_val_117_, 0);
return v_v_118_;
}
else
{
uint8_t v___x_119_; 
lean_dec(v_val_117_);
v___x_119_ = lean_unbox(v_defValue_113_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_110_ = stack[0].m_obj;
lean_object* v_opt_111_ = stack[1].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_110_, v_opt_111_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_opts_121_, lean_object* v_opt_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_121_, v_opt_122_);
lean_dec_ref(v_opt_122_);
lean_dec_ref(v_opts_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
return v___x_129_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_130_, lean_object* v_macroStack_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_scopes_136_; lean_object* v___x_137_; lean_object* v_opts_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_134_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_135_ = lean_st_ref_get(v___y_132_);
v_scopes_136_ = lean_ctor_get(v___x_135_, 2);
lean_inc(v_scopes_136_);
lean_dec(v___x_135_);
v___x_137_ = l_List_head_x21___redArg(v___x_134_, v_scopes_136_);
lean_dec(v_scopes_136_);
v_opts_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc_ref(v_opts_138_);
lean_dec(v___x_137_);
v___x_139_ = l_Lean_Elab_pp_macroStack;
v___x_140_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v_opts_138_, v___x_139_);
lean_dec_ref(v_opts_138_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_dec(v_macroStack_131_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_msgData_130_);
return v___x_141_;
}
else
{
if (lean_obj_tag(v_macroStack_131_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v_msgData_130_);
return v___x_142_;
}
else
{
lean_object* v_head_143_; lean_object* v_after_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_159_; 
v_head_143_ = lean_ctor_get(v_macroStack_131_, 0);
lean_inc(v_head_143_);
v_after_144_ = lean_ctor_get(v_head_143_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_head_143_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_head_143_, 0);
lean_dec(v_unused_160_);
v___x_146_ = v_head_143_;
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_after_144_);
lean_dec(v_head_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 7);
lean_ctor_set(v___x_146_, 1, v___x_148_);
lean_ctor_set(v___x_146_, 0, v_msgData_130_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_msgData_130_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_158_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_msgData_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_151_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_MessageData_ofSyntax(v_after_144_);
v___x_154_ = l_Lean_indentD(v___x_153_);
v_msgData_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_155_, 0, v___x_152_);
lean_ctor_set(v_msgData_155_, 1, v___x_154_);
v___x_156_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(v_msgData_155_, v_macroStack_131_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_130_ = stack[0].m_obj;
lean_object* v_macroStack_131_ = stack[1].m_obj;
lean_object* v___y_132_ = stack[2].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_130_, v_macroStack_131_, v___y_132_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_162_, lean_object* v_macroStack_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_162_, v_macroStack_163_, v___y_164_);
lean_dec(v___y_164_);
return v_res_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
lean_ctor_set(v___x_173_, 2, v___x_172_);
lean_ctor_set(v___x_173_, 3, v___x_172_);
lean_ctor_set(v___x_173_, 4, v___x_171_);
lean_ctor_set(v___x_173_, 5, v___x_171_);
lean_ctor_set(v___x_173_, 6, v___x_171_);
lean_ctor_set(v___x_173_, 7, v___x_171_);
lean_ctor_set(v___x_173_, 8, v___x_171_);
lean_ctor_set(v___x_173_, 9, v___x_171_);
lean_ctor_set(v___x_173_, 10, v___x_171_);
lean_ctor_set(v___x_173_, 11, v___x_170_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(32u);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_unsigned_to_nat(32u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_182_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_178_);
lean_ctor_set(v___x_182_, 3, v___x_178_);
lean_ctor_set_usize(v___x_182_, 4, v___x_177_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = lean_box(1);
v___x_184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_185_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_183_);
return v___x_186_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v_env_191_; uint8_t v___x_192_; lean_object* v_env_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_scopes_196_; lean_object* v___x_197_; lean_object* v_opts_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_190_ = lean_st_ref_get(v___y_188_);
v_env_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc_ref(v_env_191_);
lean_dec(v___x_190_);
v___x_192_ = 0;
v_env_193_ = l_Lean_Environment_setRecordingDeps(v_env_191_, v___x_192_);
v___x_194_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_195_ = lean_st_ref_get(v___y_188_);
v_scopes_196_ = lean_ctor_get(v___x_195_, 2);
lean_inc(v_scopes_196_);
lean_dec(v___x_195_);
v___x_197_ = l_List_head_x21___redArg(v___x_194_, v_scopes_196_);
lean_dec(v_scopes_196_);
v_opts_198_ = lean_ctor_get(v___x_197_, 1);
lean_inc_ref(v_opts_198_);
lean_dec(v___x_197_);
v___x_199_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_201_, 0, v_env_193_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v_opts_198_);
v___x_202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_msgData_187_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_187_ = stack[0].m_obj;
lean_object* v___y_188_ = stack[1].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_187_, v___y_188_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_205_, v___y_206_);
lean_dec(v___y_206_);
return v_res_208_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Elab_Command_getRef___redArg(v___y_210_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_macroStack_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v_macroStack_215_ = lean_ctor_get(v___y_210_, 4);
v___x_216_ = l_Lean_Elab_getBetterRef(v_a_214_, v_macroStack_215_);
lean_dec(v_a_214_);
v___x_217_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msg_209_, v___y_211_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref(v___x_217_);
lean_inc(v_macroStack_215_);
v___x_219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_a_218_, v_macroStack_215_, v___y_211_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_216_);
lean_ctor_set(v___x_224_, 1, v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec_ref(v_msg_209_);
v_a_229_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_213_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_213_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_209_ = stack[0].m_obj;
lean_object* v___y_210_ = stack[1].m_obj;
lean_object* v___y_211_ = stack[2].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_209_, v___y_210_, v___y_211_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg___boxed(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_242_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(lean_object* v_ref_243_, lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Elab_Command_getRef___redArg(v___y_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v_fileName_250_; lean_object* v_fileMap_251_; lean_object* v_currRecDepth_252_; lean_object* v_cmdPos_253_; lean_object* v_macroStack_254_; lean_object* v_quotContext_x3f_255_; lean_object* v_currMacroScope_256_; lean_object* v_snap_x3f_257_; lean_object* v_cancelTk_x3f_258_; uint8_t v_suppressElabErrors_259_; lean_object* v_ref_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v_fileName_250_ = lean_ctor_get(v___y_245_, 0);
v_fileMap_251_ = lean_ctor_get(v___y_245_, 1);
v_currRecDepth_252_ = lean_ctor_get(v___y_245_, 2);
v_cmdPos_253_ = lean_ctor_get(v___y_245_, 3);
v_macroStack_254_ = lean_ctor_get(v___y_245_, 4);
v_quotContext_x3f_255_ = lean_ctor_get(v___y_245_, 5);
v_currMacroScope_256_ = lean_ctor_get(v___y_245_, 6);
v_snap_x3f_257_ = lean_ctor_get(v___y_245_, 8);
v_cancelTk_x3f_258_ = lean_ctor_get(v___y_245_, 9);
v_suppressElabErrors_259_ = lean_ctor_get_uint8(v___y_245_, sizeof(void*)*10);
v_ref_260_ = l_Lean_replaceRef(v_ref_243_, v_a_249_);
lean_dec(v_a_249_);
lean_inc(v_cancelTk_x3f_258_);
lean_inc(v_snap_x3f_257_);
lean_inc(v_currMacroScope_256_);
lean_inc(v_quotContext_x3f_255_);
lean_inc(v_macroStack_254_);
lean_inc(v_cmdPos_253_);
lean_inc(v_currRecDepth_252_);
lean_inc_ref(v_fileMap_251_);
lean_inc_ref(v_fileName_250_);
v___x_261_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_261_, 0, v_fileName_250_);
lean_ctor_set(v___x_261_, 1, v_fileMap_251_);
lean_ctor_set(v___x_261_, 2, v_currRecDepth_252_);
lean_ctor_set(v___x_261_, 3, v_cmdPos_253_);
lean_ctor_set(v___x_261_, 4, v_macroStack_254_);
lean_ctor_set(v___x_261_, 5, v_quotContext_x3f_255_);
lean_ctor_set(v___x_261_, 6, v_currMacroScope_256_);
lean_ctor_set(v___x_261_, 7, v_ref_260_);
lean_ctor_set(v___x_261_, 8, v_snap_x3f_257_);
lean_ctor_set(v___x_261_, 9, v_cancelTk_x3f_258_);
lean_ctor_set_uint8(v___x_261_, sizeof(void*)*10, v_suppressElabErrors_259_);
v___x_262_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_244_, v___x_261_, v___y_246_);
lean_dec_ref_known(v___x_261_, 10);
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_msg_244_);
v_a_263_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_248_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_248_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_243_ = stack[0].m_obj;
lean_object* v_msg_244_ = stack[1].m_obj;
lean_object* v___y_245_ = stack[2].m_obj;
lean_object* v___y_246_ = stack[3].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_243_, v_msg_244_, v___y_245_, v___y_246_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg___boxed(lean_object* v_ref_272_, lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_272_, v_msg_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v_ref_272_);
return v_res_277_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__2));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(lean_object* v_stx_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1));
lean_inc(v_stx_289_);
v___x_294_ = l_Lean_Syntax_isOfKind(v_stx_289_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3);
v___x_296_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_stx_289_, v___x_295_, v_a_290_, v_a_291_);
lean_dec(v_stx_289_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v_t_301_; lean_object* v_e_x3f_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_297_ = lean_unsigned_to_nat(2u);
v___x_298_ = l_Lean_Syntax_getArg(v_stx_289_, v___x_297_);
lean_inc(v___x_298_);
v___f_299_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___lam__0___boxed), 9, 1);
lean_closure_set(v___f_299_, 0, v___x_298_);
v___x_300_ = lean_unsigned_to_nat(4u);
v_t_301_ = l_Lean_Syntax_getArg(v_stx_289_, v___x_300_);
v___x_380_ = lean_unsigned_to_nat(5u);
v___x_381_ = l_Lean_Syntax_getArg(v_stx_289_, v___x_380_);
v___x_382_ = l_Lean_Syntax_isNone(v___x_381_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
lean_inc(v___x_381_);
v___x_383_ = l_Lean_Syntax_matchesNull(v___x_381_, v___x_297_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v___x_381_);
lean_dec(v_t_301_);
lean_dec_ref(v___f_299_);
lean_dec(v___x_298_);
v___x_384_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__3);
v___x_385_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_stx_289_, v___x_384_, v_a_290_, v_a_291_);
lean_dec(v_stx_289_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; lean_object* v_e_x3f_387_; lean_object* v___x_388_; 
lean_dec(v_stx_289_);
v___x_386_ = lean_unsigned_to_nat(1u);
v_e_x3f_387_ = l_Lean_Syntax_getArg(v___x_381_, v___x_386_);
lean_dec(v___x_381_);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v_e_x3f_387_);
v_e_x3f_303_ = v___x_388_;
v___y_304_ = v_a_290_;
v___y_305_ = v_a_291_;
goto v___jp_302_;
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v___x_381_);
lean_dec(v_stx_289_);
v___x_389_ = lean_box(0);
v_e_x3f_303_ = v___x_389_;
v___y_304_ = v_a_290_;
v___y_305_ = v_a_291_;
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Elab_Command_getRef___redArg(v___y_304_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_fileName_308_; lean_object* v_fileMap_309_; lean_object* v_currRecDepth_310_; lean_object* v_cmdPos_311_; lean_object* v_macroStack_312_; lean_object* v_quotContext_x3f_313_; lean_object* v_currMacroScope_314_; lean_object* v_snap_x3f_315_; lean_object* v_cancelTk_x3f_316_; uint8_t v_suppressElabErrors_317_; lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v_fileName_308_ = lean_ctor_get(v___y_304_, 0);
v_fileMap_309_ = lean_ctor_get(v___y_304_, 1);
v_currRecDepth_310_ = lean_ctor_get(v___y_304_, 2);
v_cmdPos_311_ = lean_ctor_get(v___y_304_, 3);
v_macroStack_312_ = lean_ctor_get(v___y_304_, 4);
v_quotContext_x3f_313_ = lean_ctor_get(v___y_304_, 5);
v_currMacroScope_314_ = lean_ctor_get(v___y_304_, 6);
v_snap_x3f_315_ = lean_ctor_get(v___y_304_, 8);
v_cancelTk_x3f_316_ = lean_ctor_get(v___y_304_, 9);
v_suppressElabErrors_317_ = lean_ctor_get_uint8(v___y_304_, sizeof(void*)*10);
v_ref_318_ = l_Lean_replaceRef(v___x_298_, v_a_307_);
lean_dec(v_a_307_);
lean_dec(v___x_298_);
lean_inc(v_cancelTk_x3f_316_);
lean_inc(v_snap_x3f_315_);
lean_inc(v_currMacroScope_314_);
lean_inc(v_quotContext_x3f_313_);
lean_inc(v_macroStack_312_);
lean_inc(v_cmdPos_311_);
lean_inc(v_currRecDepth_310_);
lean_inc_ref(v_fileMap_309_);
lean_inc_ref(v_fileName_308_);
v___x_319_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_319_, 0, v_fileName_308_);
lean_ctor_set(v___x_319_, 1, v_fileMap_309_);
lean_ctor_set(v___x_319_, 2, v_currRecDepth_310_);
lean_ctor_set(v___x_319_, 3, v_cmdPos_311_);
lean_ctor_set(v___x_319_, 4, v_macroStack_312_);
lean_ctor_set(v___x_319_, 5, v_quotContext_x3f_313_);
lean_ctor_set(v___x_319_, 6, v_currMacroScope_314_);
lean_ctor_set(v___x_319_, 7, v_ref_318_);
lean_ctor_set(v___x_319_, 8, v_snap_x3f_315_);
lean_ctor_set(v___x_319_, 9, v_cancelTk_x3f_316_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*10, v_suppressElabErrors_317_);
v___x_320_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_299_, v___x_319_, v___y_305_);
lean_dec_ref_known(v___x_319_, 10);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_363_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_363_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_363_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_363_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_unbox(v_a_321_);
lean_dec(v_a_321_);
if (v___x_325_ == 0)
{
lean_dec(v_t_301_);
if (lean_obj_tag(v_e_x3f_303_) == 1)
{
lean_object* v_val_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_del_object(v___x_323_);
v_val_326_ = lean_ctor_get(v_e_x3f_303_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v_e_x3f_303_, 1);
v___x_327_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(v_val_326_);
v___x_328_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5));
v___x_329_ = lean_box(2);
v___x_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_327_);
v___x_331_ = l_Lean_Elab_Command_getRef___redArg(v___y_304_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
lean_inc_ref(v___x_330_);
v___x_333_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_333_, 0, v___x_330_);
v___x_334_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_a_332_, v___x_330_, v___x_333_, v___y_304_, v___y_305_);
return v___x_334_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec_ref_known(v___x_330_, 3);
v_a_335_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_331_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec(v_e_x3f_303_);
v___x_343_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_343_);
v___x_345_ = v___x_323_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_del_object(v___x_323_);
lean_dec(v_e_x3f_303_);
v___x_347_ = l___private_Lake_DSL_Meta_0__Lake_DSL_expandCmdDo(v_t_301_);
v___x_348_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__5));
v___x_349_ = lean_box(2);
v___x_350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_347_);
v___x_351_ = l_Lean_Elab_Command_getRef___redArg(v___y_304_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
lean_inc_ref(v___x_350_);
v___x_353_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_353_, 0, v___x_350_);
v___x_354_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_a_352_, v___x_350_, v___x_353_, v___y_304_, v___y_305_);
return v___x_354_;
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref_known(v___x_350_, 3);
v_a_355_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_351_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_e_x3f_303_);
lean_dec(v_t_301_);
v_a_364_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_320_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_320_);
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
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_e_x3f_303_);
lean_dec(v_t_301_);
lean_dec_ref(v___f_299_);
lean_dec(v___x_298_);
v_a_372_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_306_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_306_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_289_ = stack[0].m_obj;
lean_object* v_a_290_ = stack[1].m_obj;
lean_object* v_a_291_ = stack[2].m_obj;
lean_object* v_res_390_;
v_res_390_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(v_stx_289_, v_a_290_, v_a_291_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed(lean_object* v_stx_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf(v_stx_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
return v_res_395_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(lean_object* v_00_u03b1_396_, lean_object* v_ref_397_, lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___redArg(v_ref_397_, v_msg_398_, v___y_399_, v___y_400_);
return v___x_402_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_397_ = stack[1].m_obj;
lean_object* v_msg_398_ = stack[2].m_obj;
lean_object* v___y_399_ = stack[3].m_obj;
lean_object* v___y_400_ = stack[4].m_obj;
lean_object* v_res_403_;
v_res_403_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(lean_box(0), v_ref_397_, v_msg_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_403_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0___boxed(lean_object* v_00_u03b1_404_, lean_object* v_ref_405_, lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0(v_00_u03b1_404_, v_ref_405_, v_msg_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v_ref_405_);
return v_res_410_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(lean_object* v_msgData_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___redArg(v_msgData_411_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_411_ = stack[0].m_obj;
lean_object* v___y_412_ = stack[1].m_obj;
lean_object* v___y_413_ = stack[2].m_obj;
lean_object* v_res_416_;
v_res_416_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(v_msgData_411_, v___y_412_, v___y_413_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__1(v_msgData_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_421_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___redArg(v_msg_423_, v___y_424_, v___y_425_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_423_ = stack[1].m_obj;
lean_object* v___y_424_ = stack[2].m_obj;
lean_object* v___y_425_ = stack[3].m_obj;
lean_object* v_res_428_;
v_res_428_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(lean_box(0), v_msg_423_, v___y_424_, v___y_425_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0(v_00_u03b1_429_, v_msg_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_434_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(lean_object* v_msgData_435_, lean_object* v_macroStack_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg(v_msgData_435_, v_macroStack_436_, v___y_438_);
return v___x_440_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_435_ = stack[0].m_obj;
lean_object* v_macroStack_436_ = stack[1].m_obj;
lean_object* v___y_437_ = stack[2].m_obj;
lean_object* v___y_438_ = stack[3].m_obj;
lean_object* v_res_441_;
v_res_441_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(v_msgData_435_, v_macroStack_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_442_, lean_object* v_macroStack_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2(v_msgData_442_, v_macroStack_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_447_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1(){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_477_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___closed__1));
v___x_478_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___closed__10));
v___x_479_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___boxed), 4, 0);
v___x_480_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_476_, v___x_477_, v___x_478_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_481_;
v_res_481_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1___boxed(lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf__1();
return v_res_483_;
}
}
lean_object* l_Lake_DSL_toExprIO___redArg(lean_object* v_inst_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_toExpr_487_; lean_object* v___x_488_; 
v_toExpr_487_ = lean_ctor_get(v_inst_484_, 0);
lean_inc_ref(v_toExpr_487_);
lean_dec_ref(v_inst_484_);
v___x_488_ = lean_apply_1(v_x_485_, lean_box(0));
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_apply_1(v_toExpr_487_, v_a_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_toExpr_487_);
v_a_498_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_488_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_DSL_toExprIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_484_ = stack[0].m_obj;
lean_object* v_x_485_ = stack[1].m_obj;
lean_object* v_res_506_;
v_res_506_ = l_Lake_DSL_toExprIO___redArg(v_inst_484_, v_x_485_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___redArg___boxed(lean_object* v_inst_507_, lean_object* v_x_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lake_DSL_toExprIO___redArg(v_inst_507_, v_x_508_);
return v_res_510_;
}
}
lean_object* l_Lake_DSL_toExprIO(lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lake_DSL_toExprIO___redArg(v_inst_512_, v_x_513_);
return v___x_515_;
}
}
LEAN_EXPORT void l_Lake_DSL_toExprIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_512_ = stack[1].m_obj;
lean_object* v_x_513_ = stack[2].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Lake_DSL_toExprIO(lean_box(0), v_inst_512_, v_x_513_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Lake_DSL_toExprIO___boxed(lean_object* v_00_u03b1_517_, lean_object* v_inst_518_, lean_object* v_x_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lake_DSL_toExprIO(v_00_u03b1_517_, v_inst_518_, v_x_519_);
return v_res_521_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_box(0);
v___x_526_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__1));
v___x_527_ = l_Lean_mkConst(v___x_526_, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_box(0);
v___x_534_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__5));
v___x_535_ = l_Lean_mkConst(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__6);
v___x_537_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2);
v___x_538_ = l_Lean_Expr_app___override(v___x_537_, v___x_536_);
return v___x_538_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(lean_object* v_v_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; 
v___x_545_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7);
v___x_546_ = 1;
v___x_547_ = 1;
v___x_548_ = l_Lean_Meta_evalExpr___redArg(v___x_545_, v_v_539_, v___x_546_, v___x_547_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
return v___x_548_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_539_ = stack[0].m_obj;
lean_object* v_a_540_ = stack[1].m_obj;
lean_object* v_a_541_ = stack[2].m_obj;
lean_object* v_a_542_ = stack[3].m_obj;
lean_object* v_a_543_ = stack[4].m_obj;
lean_object* v_res_549_;
v_res_549_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(v_v_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___boxed(lean_object* v_v_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1(v_v_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_556_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
return v___x_559_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg(){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___closed__0);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_563_;
v_res_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
stack->m_obj
 = v_res_563_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg___boxed(lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
return v_res_565_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(lean_object* v_00_u03b1_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
return v___x_574_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_567_ = stack[1].m_obj;
lean_object* v___y_568_ = stack[2].m_obj;
lean_object* v___y_569_ = stack[3].m_obj;
lean_object* v___y_570_ = stack[4].m_obj;
lean_object* v___y_571_ = stack[5].m_obj;
lean_object* v___y_572_ = stack[6].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(lean_box(0), v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___boxed(lean_object* v_00_u03b1_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0(v_00_u03b1_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_584_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(lean_object* v_e_585_, lean_object* v___y_586_){
_start:
{
uint8_t v___x_588_; 
v___x_588_ = l_Lean_Expr_hasMVar(v_e_585_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_e_585_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v_mctx_591_; lean_object* v___x_592_; lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v___x_595_; lean_object* v_cache_596_; lean_object* v_zetaDeltaFVarIds_597_; lean_object* v_postponed_598_; lean_object* v_diag_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
v___x_590_ = lean_st_ref_get(v___y_586_);
v_mctx_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc_ref(v_mctx_591_);
lean_dec(v___x_590_);
v___x_592_ = l_Lean_instantiateMVarsCore(v_mctx_591_, v_e_585_);
v_fst_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_fst_593_);
v_snd_594_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_snd_594_);
lean_dec_ref(v___x_592_);
v___x_595_ = lean_st_ref_take(v___y_586_);
v_cache_596_ = lean_ctor_get(v___x_595_, 1);
v_zetaDeltaFVarIds_597_ = lean_ctor_get(v___x_595_, 2);
v_postponed_598_ = lean_ctor_get(v___x_595_, 3);
v_diag_599_ = lean_ctor_get(v___x_595_, 4);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_609_);
v___x_601_ = v___x_595_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_diag_599_);
lean_inc(v_postponed_598_);
lean_inc(v_zetaDeltaFVarIds_597_);
lean_inc(v_cache_596_);
lean_dec(v___x_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_snd_594_);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_snd_594_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_cache_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_zetaDeltaFVarIds_597_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_postponed_598_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_diag_599_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_st_ref_put(v___y_586_, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_fst_593_);
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_585_ = stack[0].m_obj;
lean_object* v___y_586_ = stack[1].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_585_, v___y_586_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg___boxed(lean_object* v_e_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_611_, v___y_612_);
lean_dec(v___y_612_);
return v_res_614_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_e_615_, v___y_619_);
return v___x_623_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_615_ = stack[0].m_obj;
lean_object* v___y_616_ = stack[1].m_obj;
lean_object* v___y_617_ = stack[2].m_obj;
lean_object* v___y_618_ = stack[3].m_obj;
lean_object* v___y_619_ = stack[4].m_obj;
lean_object* v___y_620_ = stack[5].m_obj;
lean_object* v___y_621_ = stack[6].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(v_e_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___boxed(lean_object* v_e_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1(v_e_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_633_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Lean_Elab_abortTermExceptionId;
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_634_);
return v___x_636_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg(){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___closed__0);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_640_;
v_res_640_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg___boxed(lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
return v_res_642_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(lean_object* v_00_u03b1_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
return v___x_651_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_644_ = stack[1].m_obj;
lean_object* v___y_645_ = stack[2].m_obj;
lean_object* v___y_646_ = stack[3].m_obj;
lean_object* v___y_647_ = stack[4].m_obj;
lean_object* v___y_648_ = stack[5].m_obj;
lean_object* v___y_649_ = stack[6].m_obj;
lean_object* v_res_652_;
v_res_652_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(lean_box(0), v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___boxed(lean_object* v_00_u03b1_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5(v_00_u03b1_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_661_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(lean_object* v_a_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = lean_apply_1(v_a_662_, lean_box(0));
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
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
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_688_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_662_ = stack[0].m_obj;
lean_object* v___y_663_ = stack[1].m_obj;
lean_object* v___y_664_ = stack[2].m_obj;
lean_object* v___y_665_ = stack[3].m_obj;
lean_object* v___y_666_ = stack[4].m_obj;
lean_object* v___y_667_ = stack[5].m_obj;
lean_object* v___y_668_ = stack[6].m_obj;
lean_object* v_res_689_;
v_res_689_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(v_a_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed(lean_object* v_a_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0(v_a_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_698_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(lean_object* v_msgData_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v_env_706_; uint8_t v___x_707_; lean_object* v_env_708_; lean_object* v___x_709_; lean_object* v_toCold_710_; lean_object* v_mctx_711_; lean_object* v_lctx_712_; lean_object* v_options_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_705_ = lean_st_ref_get(v___y_703_);
v_env_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_ref(v_env_706_);
lean_dec(v___x_705_);
v___x_707_ = 0;
v_env_708_ = l_Lean_Environment_setRecordingDeps(v_env_706_, v___x_707_);
v___x_709_ = lean_st_ref_get(v___y_701_);
v_toCold_710_ = lean_ctor_get(v___y_702_, 0);
v_mctx_711_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_mctx_711_);
lean_dec(v___x_709_);
v_lctx_712_ = lean_ctor_get(v___y_700_, 2);
v_options_713_ = lean_ctor_get(v_toCold_710_, 2);
lean_inc_ref(v_options_713_);
lean_inc_ref(v_lctx_712_);
v___x_714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_714_, 0, v_env_708_);
lean_ctor_set(v___x_714_, 1, v_mctx_711_);
lean_ctor_set(v___x_714_, 2, v_lctx_712_);
lean_ctor_set(v___x_714_, 3, v_options_713_);
v___x_715_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_msgData_699_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_699_ = stack[0].m_obj;
lean_object* v___y_700_ = stack[1].m_obj;
lean_object* v___y_701_ = stack[2].m_obj;
lean_object* v___y_702_ = stack[3].m_obj;
lean_object* v___y_703_ = stack[4].m_obj;
lean_object* v_res_717_;
v_res_717_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msgData_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9___boxed(lean_object* v_msgData_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msgData_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(uint8_t v_suppressElabErrors_733_, uint8_t v___y_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 1)
{
lean_object* v_pre_736_; 
v_pre_736_ = lean_ctor_get(v_x_735_, 0);
switch(lean_obj_tag(v_pre_736_))
{
case 1:
{
lean_object* v_pre_737_; 
v_pre_737_ = lean_ctor_get(v_pre_736_, 0);
switch(lean_obj_tag(v_pre_737_))
{
case 0:
{
lean_object* v_str_738_; lean_object* v_str_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_str_738_ = lean_ctor_get(v_x_735_, 1);
v_str_739_ = lean_ctor_get(v_pre_736_, 1);
v___x_740_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__0));
v___x_741_ = lean_string_dec_eq(v_str_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__1));
v___x_743_ = lean_string_dec_eq(v_str_739_, v___x_742_);
if (v___x_743_ == 0)
{
return v___x_743_;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__2));
v___x_745_ = lean_string_dec_eq(v_str_738_, v___x_744_);
if (v___x_745_ == 0)
{
return v___x_745_;
}
else
{
return v_suppressElabErrors_733_;
}
}
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__3));
v___x_747_ = lean_string_dec_eq(v_str_738_, v___x_746_);
if (v___x_747_ == 0)
{
return v___x_747_;
}
else
{
return v_suppressElabErrors_733_;
}
}
}
case 1:
{
lean_object* v_pre_748_; 
v_pre_748_ = lean_ctor_get(v_pre_737_, 0);
if (lean_obj_tag(v_pre_748_) == 0)
{
lean_object* v_str_749_; lean_object* v_str_750_; lean_object* v_str_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_str_749_ = lean_ctor_get(v_x_735_, 1);
v_str_750_ = lean_ctor_get(v_pre_736_, 1);
v_str_751_ = lean_ctor_get(v_pre_737_, 1);
v___x_752_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__4));
v___x_753_ = lean_string_dec_eq(v_str_751_, v___x_752_);
if (v___x_753_ == 0)
{
return v___x_753_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__5));
v___x_755_ = lean_string_dec_eq(v_str_750_, v___x_754_);
if (v___x_755_ == 0)
{
return v___x_755_;
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__6));
v___x_757_ = lean_string_dec_eq(v_str_749_, v___x_756_);
if (v___x_757_ == 0)
{
return v___x_757_;
}
else
{
return v_suppressElabErrors_733_;
}
}
}
}
else
{
return v___y_734_;
}
}
default: 
{
return v___y_734_;
}
}
}
case 0:
{
lean_object* v_str_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_str_758_ = lean_ctor_get(v_x_735_, 1);
v___x_759_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___closed__7));
v___x_760_ = lean_string_dec_eq(v_str_758_, v___x_759_);
if (v___x_760_ == 0)
{
return v___x_760_;
}
else
{
return v_suppressElabErrors_733_;
}
}
default: 
{
return v___y_734_;
}
}
}
else
{
return v___y_734_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_733_ = stack[0].m_num;
uint8_t v___y_734_ = stack[1].m_num;
lean_object* v_x_735_ = stack[2].m_obj;
uint8_t v_res_761_;
v_res_761_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(v_suppressElabErrors_733_, v___y_734_, v_x_735_);
stack->m_num = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_762_, lean_object* v___y_763_, lean_object* v_x_764_){
_start:
{
uint8_t v_suppressElabErrors_boxed_765_; uint8_t v___y_21263__boxed_766_; uint8_t v_res_767_; lean_object* v_r_768_; 
v_suppressElabErrors_boxed_765_ = lean_unbox(v_suppressElabErrors_762_);
v___y_21263__boxed_766_ = lean_unbox(v___y_763_);
v_res_767_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0(v_suppressElabErrors_boxed_765_, v___y_21263__boxed_766_, v_x_764_);
lean_dec(v_x_764_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(lean_object* v_ref_770_, lean_object* v_msgData_771_, uint8_t v_severity_772_, uint8_t v_isSilent_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
uint8_t v___y_780_; lean_object* v___y_781_; uint8_t v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_toCold_787_; lean_object* v___y_788_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_819_; uint8_t v___y_820_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_844_; uint8_t v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_848_; uint8_t v___y_849_; lean_object* v___y_850_; uint8_t v___y_854_; uint8_t v___y_855_; uint8_t v___y_856_; uint8_t v___x_867_; uint8_t v___y_869_; uint8_t v___y_870_; uint8_t v___y_871_; uint8_t v___y_873_; uint8_t v___x_881_; 
v___x_867_ = 2;
v___x_881_ = l_Lean_instBEqMessageSeverity_beq(v_severity_772_, v___x_867_);
if (v___x_881_ == 0)
{
v___y_873_ = v___x_881_;
goto v___jp_872_;
}
else
{
uint8_t v___x_882_; 
lean_inc_ref(v_msgData_771_);
v___x_882_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_771_);
v___y_873_ = v___x_882_;
goto v___jp_872_;
}
v___jp_779_:
{
lean_object* v_currNamespace_789_; lean_object* v_openDecls_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_env_795_; lean_object* v_nextMacroScope_796_; lean_object* v_ngen_797_; lean_object* v_auxDeclNGen_798_; lean_object* v_traceState_799_; lean_object* v_cache_800_; lean_object* v_recordedDeps_801_; lean_object* v_messages_802_; lean_object* v_infoState_803_; lean_object* v_snapshotTasks_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_815_; 
v_currNamespace_789_ = lean_ctor_get(v_toCold_787_, 4);
v_openDecls_790_ = lean_ctor_get(v_toCold_787_, 5);
lean_inc(v_openDecls_790_);
lean_inc(v_currNamespace_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_currNamespace_789_);
lean_ctor_set(v___x_791_, 1, v_openDecls_790_);
v___x_792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___y_785_);
lean_inc_ref(v___y_783_);
lean_inc_ref(v___y_781_);
v___x_793_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_793_, 0, v___y_781_);
lean_ctor_set(v___x_793_, 1, v___y_784_);
lean_ctor_set(v___x_793_, 2, v___y_786_);
lean_ctor_set(v___x_793_, 3, v___y_783_);
lean_ctor_set(v___x_793_, 4, v___x_792_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*5, v___y_782_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*5 + 1, v___y_780_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*5 + 2, v_isSilent_773_);
v___x_794_ = lean_st_ref_take(v___y_788_);
v_env_795_ = lean_ctor_get(v___x_794_, 0);
v_nextMacroScope_796_ = lean_ctor_get(v___x_794_, 1);
v_ngen_797_ = lean_ctor_get(v___x_794_, 2);
v_auxDeclNGen_798_ = lean_ctor_get(v___x_794_, 3);
v_traceState_799_ = lean_ctor_get(v___x_794_, 4);
v_cache_800_ = lean_ctor_get(v___x_794_, 5);
v_recordedDeps_801_ = lean_ctor_get(v___x_794_, 6);
v_messages_802_ = lean_ctor_get(v___x_794_, 7);
v_infoState_803_ = lean_ctor_get(v___x_794_, 8);
v_snapshotTasks_804_ = lean_ctor_get(v___x_794_, 9);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_815_ == 0)
{
v___x_806_ = v___x_794_;
v_isShared_807_ = v_isSharedCheck_815_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snapshotTasks_804_);
lean_inc(v_infoState_803_);
lean_inc(v_messages_802_);
lean_inc(v_recordedDeps_801_);
lean_inc(v_cache_800_);
lean_inc(v_traceState_799_);
lean_inc(v_auxDeclNGen_798_);
lean_inc(v_ngen_797_);
lean_inc(v_nextMacroScope_796_);
lean_inc(v_env_795_);
lean_dec(v___x_794_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_815_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_Lean_MessageLog_add(v___x_793_, v_messages_802_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 7, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_env_795_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_nextMacroScope_796_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_ngen_797_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_auxDeclNGen_798_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_traceState_799_);
lean_ctor_set(v_reuseFailAlloc_814_, 5, v_cache_800_);
lean_ctor_set(v_reuseFailAlloc_814_, 6, v_recordedDeps_801_);
lean_ctor_set(v_reuseFailAlloc_814_, 7, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_814_, 8, v_infoState_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 9, v_snapshotTasks_804_);
v___x_811_ = v_reuseFailAlloc_814_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_st_ref_put(v___y_788_, v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_808_);
return v___x_813_;
}
}
}
v___jp_816_:
{
lean_object* v_fileName_825_; lean_object* v_fileMap_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
v_fileName_825_ = lean_ctor_get(v___y_823_, 0);
v_fileMap_826_ = lean_ctor_get(v___y_823_, 1);
v___x_827_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_771_);
v___x_828_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v___x_827_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_842_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc_ref_n(v_fileMap_826_, 2);
v___x_833_ = l_Lean_FileMap_toPosition(v_fileMap_826_, v___y_822_);
lean_dec(v___y_822_);
v___x_834_ = l_Lean_FileMap_toPosition(v_fileMap_826_, v___y_824_);
lean_dec(v___y_824_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0));
if (v___y_820_ == 0)
{
lean_del_object(v___x_831_);
lean_dec_ref(v___y_817_);
v___y_780_ = v___y_819_;
v___y_781_ = v_fileName_825_;
v___y_782_ = v___y_821_;
v___y_783_ = v___x_836_;
v___y_784_ = v___x_833_;
v___y_785_ = v_a_829_;
v___y_786_ = v___x_835_;
v_toCold_787_ = v___y_818_;
v___y_788_ = v___y_777_;
goto v___jp_779_;
}
else
{
uint8_t v___x_837_; 
lean_inc(v_a_829_);
v___x_837_ = l_Lean_MessageData_hasTag(v___y_817_, v_a_829_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec_ref_known(v___x_835_, 1);
lean_dec_ref(v___x_833_);
lean_dec(v_a_829_);
v___x_838_ = lean_box(0);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_del_object(v___x_831_);
v___y_780_ = v___y_819_;
v___y_781_ = v_fileName_825_;
v___y_782_ = v___y_821_;
v___y_783_ = v___x_836_;
v___y_784_ = v___x_833_;
v___y_785_ = v_a_829_;
v___y_786_ = v___x_835_;
v_toCold_787_ = v___y_818_;
v___y_788_ = v___y_777_;
goto v___jp_779_;
}
}
}
}
v___jp_843_:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Syntax_getTailPos_x3f(v___y_847_, v___y_849_);
lean_dec(v___y_847_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_inc(v___y_850_);
v___y_817_ = v___y_844_;
v___y_818_ = v___y_846_;
v___y_819_ = v___y_848_;
v___y_820_ = v___y_845_;
v___y_821_ = v___y_849_;
v___y_822_ = v___y_850_;
v___y_823_ = v___y_846_;
v___y_824_ = v___y_850_;
goto v___jp_816_;
}
else
{
lean_object* v_val_852_; 
v_val_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v___x_851_, 1);
v___y_817_ = v___y_844_;
v___y_818_ = v___y_846_;
v___y_819_ = v___y_848_;
v___y_820_ = v___y_845_;
v___y_821_ = v___y_849_;
v___y_822_ = v___y_850_;
v___y_823_ = v___y_846_;
v___y_824_ = v_val_852_;
goto v___jp_816_;
}
}
v___jp_853_:
{
lean_object* v_toCold_857_; lean_object* v_ref_858_; uint8_t v_suppressElabErrors_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v_ref_863_; lean_object* v___x_864_; 
v_toCold_857_ = lean_ctor_get(v___y_776_, 0);
v_ref_858_ = lean_ctor_get(v___y_776_, 2);
v_suppressElabErrors_859_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*3 + 2);
v___x_860_ = lean_box(v_suppressElabErrors_859_);
v___x_861_ = lean_box(v___y_854_);
v___f_862_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_862_, 0, v___x_860_);
lean_closure_set(v___f_862_, 1, v___x_861_);
v_ref_863_ = l_Lean_replaceRef(v_ref_770_, v_ref_858_);
v___x_864_ = l_Lean_Syntax_getPos_x3f(v_ref_863_, v___y_855_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; 
v___x_865_ = lean_unsigned_to_nat(0u);
v___y_844_ = v___f_862_;
v___y_845_ = v_suppressElabErrors_859_;
v___y_846_ = v_toCold_857_;
v___y_847_ = v_ref_863_;
v___y_848_ = v___y_856_;
v___y_849_ = v___y_855_;
v___y_850_ = v___x_865_;
goto v___jp_843_;
}
else
{
lean_object* v_val_866_; 
v_val_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v___x_864_, 1);
v___y_844_ = v___f_862_;
v___y_845_ = v_suppressElabErrors_859_;
v___y_846_ = v_toCold_857_;
v___y_847_ = v_ref_863_;
v___y_848_ = v___y_856_;
v___y_849_ = v___y_855_;
v___y_850_ = v_val_866_;
goto v___jp_843_;
}
}
v___jp_868_:
{
if (v___y_871_ == 0)
{
v___y_854_ = v___y_869_;
v___y_855_ = v___y_870_;
v___y_856_ = v_severity_772_;
goto v___jp_853_;
}
else
{
v___y_854_ = v___y_869_;
v___y_855_ = v___y_870_;
v___y_856_ = v___x_867_;
goto v___jp_853_;
}
}
v___jp_872_:
{
if (v___y_873_ == 0)
{
uint8_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = 1;
v___x_875_ = l_Lean_instBEqMessageSeverity_beq(v_severity_772_, v___x_874_);
if (v___x_875_ == 0)
{
v___y_869_ = v___y_873_;
v___y_870_ = v___y_873_;
v___y_871_ = v___x_875_;
goto v___jp_868_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_776_);
v___x_877_ = l_Lean_warningAsError;
v___x_878_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v___x_876_, v___x_877_);
lean_dec_ref(v___x_876_);
v___y_869_ = v___y_873_;
v___y_870_ = v___y_873_;
v___y_871_ = v___x_878_;
goto v___jp_868_;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v_msgData_771_);
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_770_ = stack[0].m_obj;
lean_object* v_msgData_771_ = stack[1].m_obj;
uint8_t v_severity_772_ = stack[2].m_num;
uint8_t v_isSilent_773_ = stack[3].m_num;
lean_object* v___y_774_ = stack[4].m_obj;
lean_object* v___y_775_ = stack[5].m_obj;
lean_object* v___y_776_ = stack[6].m_obj;
lean_object* v___y_777_ = stack[7].m_obj;
lean_object* v_res_883_;
v_res_883_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_770_, v_msgData_771_, v_severity_772_, v_isSilent_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___boxed(lean_object* v_ref_884_, lean_object* v_msgData_885_, lean_object* v_severity_886_, lean_object* v_isSilent_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v_severity_boxed_893_; uint8_t v_isSilent_boxed_894_; lean_object* v_res_895_; 
v_severity_boxed_893_ = lean_unbox(v_severity_886_);
v_isSilent_boxed_894_ = lean_unbox(v_isSilent_887_);
v_res_895_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_884_, v_msgData_885_, v_severity_boxed_893_, v_isSilent_boxed_894_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v_ref_884_);
return v_res_895_;
}
}
lean_object* l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(lean_object* v_ref_896_, lean_object* v_msgData_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; 
v___x_905_ = 0;
v___x_906_ = 0;
v___x_907_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_896_, v_msgData_897_, v___x_905_, v___x_906_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_907_;
}
}
LEAN_EXPORT void l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_896_ = stack[0].m_obj;
lean_object* v_msgData_897_ = stack[1].m_obj;
lean_object* v___y_898_ = stack[2].m_obj;
lean_object* v___y_899_ = stack[3].m_obj;
lean_object* v___y_900_ = stack[4].m_obj;
lean_object* v___y_901_ = stack[5].m_obj;
lean_object* v___y_902_ = stack[6].m_obj;
lean_object* v___y_903_ = stack[7].m_obj;
lean_object* v_res_908_;
v_res_908_ = l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(v_ref_896_, v_msgData_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4___boxed(lean_object* v_ref_909_, lean_object* v_msgData_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(v_ref_909_, v_msgData_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v_ref_909_);
return v_res_918_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(lean_object* v_msgData_919_, lean_object* v_macroStack_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_921_);
v___x_924_ = l_Lean_Elab_pp_macroStack;
v___x_925_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__3(v___x_923_, v___x_924_);
lean_dec_ref(v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec(v_macroStack_920_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_msgData_919_);
return v___x_926_;
}
else
{
if (lean_obj_tag(v_macroStack_920_) == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_msgData_919_);
return v___x_927_;
}
else
{
lean_object* v_head_928_; lean_object* v_after_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_944_; 
v_head_928_ = lean_ctor_get(v_macroStack_920_, 0);
lean_inc(v_head_928_);
v_after_929_ = lean_ctor_get(v_head_928_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_head_928_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_head_928_, 0);
lean_dec(v_unused_945_);
v___x_931_ = v_head_928_;
v_isShared_932_ = v_isSharedCheck_944_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_after_929_);
lean_dec(v_head_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_944_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4___closed__0);
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 7);
lean_ctor_set(v___x_931_, 1, v___x_933_);
lean_ctor_set(v___x_931_, 0, v_msgData_919_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_msgData_919_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_943_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_msgData_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_936_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_MessageData_ofSyntax(v_after_929_);
v___x_939_ = l_Lean_indentD(v___x_938_);
v_msgData_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_940_, 0, v___x_937_);
lean_ctor_set(v_msgData_940_, 1, v___x_939_);
v___x_941_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabMetaIf_spec__0_spec__0_spec__2_spec__4(v_msgData_940_, v_macroStack_920_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_919_ = stack[0].m_obj;
lean_object* v_macroStack_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v_res_946_;
v_res_946_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_919_, v_macroStack_920_, v___y_921_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_msgData_947_, lean_object* v_macroStack_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_947_, v_macroStack_948_, v___y_949_);
lean_dec_ref(v___y_949_);
return v_res_951_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_ref_960_; lean_object* v_macroStack_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
v_ref_960_ = lean_ctor_get(v___y_957_, 2);
v_macroStack_961_ = lean_ctor_get(v___y_953_, 1);
v___x_962_ = l_Lean_Elab_getBetterRef(v_ref_960_, v_macroStack_961_);
v___x_963_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__9(v_msg_952_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v___x_963_);
lean_inc(v_macroStack_961_);
v___x_965_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_a_964_, v_macroStack_961_, v___y_957_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_974_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_962_);
lean_ctor_set(v___x_970_, 1, v_a_966_);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 1);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_952_ = stack[0].m_obj;
lean_object* v___y_953_ = stack[1].m_obj;
lean_object* v___y_954_ = stack[2].m_obj;
lean_object* v___y_955_ = stack[3].m_obj;
lean_object* v___y_956_ = stack[4].m_obj;
lean_object* v___y_957_ = stack[5].m_obj;
lean_object* v___y_958_ = stack[6].m_obj;
lean_object* v_res_975_;
v_res_975_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg___boxed(lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_984_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(lean_object* v_ref_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_toCold_994_; lean_object* v_currRecDepth_995_; lean_object* v_ref_996_; uint16_t v_optionFlags_997_; uint8_t v_suppressElabErrors_998_; uint8_t v_isRecordingDeps_999_; lean_object* v_ref_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_toCold_994_ = lean_ctor_get(v___y_991_, 0);
v_currRecDepth_995_ = lean_ctor_get(v___y_991_, 1);
v_ref_996_ = lean_ctor_get(v___y_991_, 2);
v_optionFlags_997_ = lean_ctor_get_uint16(v___y_991_, sizeof(void*)*3);
v_suppressElabErrors_998_ = lean_ctor_get_uint8(v___y_991_, sizeof(void*)*3 + 2);
v_isRecordingDeps_999_ = lean_ctor_get_uint8(v___y_991_, sizeof(void*)*3 + 3);
v_ref_1000_ = l_Lean_replaceRef(v_ref_985_, v_ref_996_);
lean_inc(v_currRecDepth_995_);
lean_inc_ref(v_toCold_994_);
v___x_1001_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1001_, 0, v_toCold_994_);
lean_ctor_set(v___x_1001_, 1, v_currRecDepth_995_);
lean_ctor_set(v___x_1001_, 2, v_ref_1000_);
lean_ctor_set_uint16(v___x_1001_, sizeof(void*)*3, v_optionFlags_997_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*3 + 2, v_suppressElabErrors_998_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*3 + 3, v_isRecordingDeps_999_);
v___x_1002_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___x_1001_, v___y_992_);
lean_dec_ref_known(v___x_1001_, 3);
return v___x_1002_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_985_ = stack[0].m_obj;
lean_object* v_msg_986_ = stack[1].m_obj;
lean_object* v___y_987_ = stack[2].m_obj;
lean_object* v___y_988_ = stack[3].m_obj;
lean_object* v___y_989_ = stack[4].m_obj;
lean_object* v___y_990_ = stack[5].m_obj;
lean_object* v___y_991_ = stack[6].m_obj;
lean_object* v___y_992_ = stack[7].m_obj;
lean_object* v_res_1003_;
v_res_1003_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_ref_985_, v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg___boxed(lean_object* v_ref_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_ref_1004_, v_msg_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_ref_1004_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(lean_object* v_msg_1014_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg___closed__0));
v___x_1016_ = lean_panic_fn_borrowed(v___x_1015_, v_msg_1014_);
return v___x_1016_;
}
}
lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(lean_object* v_val_1017_, lean_object* v___x_1018_, lean_object* v_a_x3f_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_get_set_stderr(v_val_1017_);
lean_dec_ref(v___x_1021_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1018_);
return v___x_1022_;
}
}
LEAN_EXPORT void l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1017_ = stack[0].m_obj;
lean_object* v___x_1018_ = stack[1].m_obj;
lean_object* v_a_x3f_1019_ = stack[2].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v_val_1017_, v___x_1018_, v_a_x3f_1019_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_val_1024_, lean_object* v___x_1025_, lean_object* v_a_x3f_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v_val_1024_, v___x_1025_, v_a_x3f_1026_);
lean_dec(v_a_x3f_1026_);
return v_res_1028_;
}
}
lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(lean_object* v_h_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_r_1040_; 
v___x_1038_ = lean_get_set_stderr(v_h_1029_);
v___x_1039_ = lean_box(0);
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
v_r_1040_ = lean_apply_7(v_x_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, lean_box(0));
if (lean_obj_tag(v_r_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1057_; 
v_a_1041_ = lean_ctor_get(v_r_1040_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_r_1040_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1043_ = v_r_1040_;
v_isShared_1044_ = v_isSharedCheck_1057_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v_r_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1057_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
lean_inc(v_a_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v___x_1047_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v___x_1038_, v___x_1039_, v___x_1046_);
lean_dec_ref(v___x_1046_);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1047_, 0);
lean_dec(v_unused_1055_);
v___x_1049_ = v___x_1047_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v___x_1047_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_a_1041_);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1041_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1058_ = lean_ctor_get(v_r_1040_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v_r_1040_, 1);
v___x_1059_ = lean_box(0);
v___x_1060_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___lam__0(v___x_1038_, v___x_1039_, v___x_1059_);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1060_, 0);
lean_dec(v_unused_1068_);
v___x_1062_ = v___x_1060_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1060_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
lean_ctor_set(v___x_1062_, 0, v_a_1058_);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1058_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT void l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1029_ = stack[0].m_obj;
lean_object* v_x_1030_ = stack[1].m_obj;
lean_object* v___y_1031_ = stack[2].m_obj;
lean_object* v___y_1032_ = stack[3].m_obj;
lean_object* v___y_1033_ = stack[4].m_obj;
lean_object* v___y_1034_ = stack[5].m_obj;
lean_object* v___y_1035_ = stack[6].m_obj;
lean_object* v___y_1036_ = stack[7].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_1029_, v_x_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg___boxed(lean_object* v_h_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_1070_, v_x_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1079_;
}
}
lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(lean_object* v_00_u03b1_1080_, lean_object* v_h_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___redArg(v_h_1081_, v_x_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT void l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1081_ = stack[1].m_obj;
lean_object* v_x_1082_ = stack[2].m_obj;
lean_object* v___y_1083_ = stack[3].m_obj;
lean_object* v___y_1084_ = stack[4].m_obj;
lean_object* v___y_1085_ = stack[5].m_obj;
lean_object* v___y_1086_ = stack[6].m_obj;
lean_object* v___y_1087_ = stack[7].m_obj;
lean_object* v___y_1088_ = stack[8].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(lean_box(0), v_h_1081_, v_x_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_h_1093_, lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5(v_00_u03b1_1092_, v_h_1093_, v_x_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1102_;
}
}
lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(lean_object* v_val_1103_, lean_object* v___x_1104_, lean_object* v_a_x3f_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_get_set_stdin(v_val_1103_);
lean_dec_ref(v___x_1107_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1104_);
return v___x_1108_;
}
}
LEAN_EXPORT void l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1103_ = stack[0].m_obj;
lean_object* v___x_1104_ = stack[1].m_obj;
lean_object* v_a_x3f_1105_ = stack[2].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v_val_1103_, v___x_1104_, v_a_x3f_1105_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_val_1110_, lean_object* v___x_1111_, lean_object* v_a_x3f_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v_val_1110_, v___x_1111_, v_a_x3f_1112_);
lean_dec(v_a_x3f_1112_);
return v_res_1114_;
}
}
lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(lean_object* v_h_1115_, lean_object* v_x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_r_1126_; 
v___x_1124_ = lean_get_set_stdin(v_h_1115_);
v___x_1125_ = lean_box(0);
lean_inc(v___y_1122_);
lean_inc_ref(v___y_1121_);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
v_r_1126_ = lean_apply_7(v_x_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, lean_box(0));
if (lean_obj_tag(v_r_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1143_; 
v_a_1127_ = lean_ctor_get(v_r_1126_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_r_1126_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1129_ = v_r_1126_;
v_isShared_1130_ = v_isSharedCheck_1143_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v_r_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1143_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
lean_inc(v_a_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 1);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v___x_1133_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v___x_1124_, v___x_1125_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v___x_1133_, 0);
lean_dec(v_unused_1141_);
v___x_1135_ = v___x_1133_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v___x_1133_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_a_1127_);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1127_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1144_ = lean_ctor_get(v_r_1126_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v_r_1126_, 1);
v___x_1145_ = lean_box(0);
v___x_1146_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___lam__0(v___x_1124_, v___x_1125_, v___x_1145_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1144_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT void l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1115_ = stack[0].m_obj;
lean_object* v_x_1116_ = stack[1].m_obj;
lean_object* v___y_1117_ = stack[2].m_obj;
lean_object* v___y_1118_ = stack[3].m_obj;
lean_object* v___y_1119_ = stack[4].m_obj;
lean_object* v___y_1120_ = stack[5].m_obj;
lean_object* v___y_1121_ = stack[6].m_obj;
lean_object* v___y_1122_ = stack[7].m_obj;
lean_object* v_res_1155_;
v_res_1155_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_1115_, v_x_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
stack->m_obj
 = v_res_1155_;
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg___boxed(lean_object* v_h_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_1156_, v_x_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1165_;
}
}
lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(lean_object* v_val_1166_, lean_object* v___x_1167_, lean_object* v_a_x3f_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_get_set_stdout(v_val_1166_);
lean_dec_ref(v___x_1170_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1167_);
return v___x_1171_;
}
}
LEAN_EXPORT void l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1166_ = stack[0].m_obj;
lean_object* v___x_1167_ = stack[1].m_obj;
lean_object* v_a_x3f_1168_ = stack[2].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v_val_1166_, v___x_1167_, v_a_x3f_1168_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_val_1173_, lean_object* v___x_1174_, lean_object* v_a_x3f_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v_val_1173_, v___x_1174_, v_a_x3f_1175_);
lean_dec(v_a_x3f_1175_);
return v_res_1177_;
}
}
lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(lean_object* v_h_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_r_1189_; 
v___x_1187_ = lean_get_set_stdout(v_h_1178_);
v___x_1188_ = lean_box(0);
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
v_r_1189_ = lean_apply_7(v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, lean_box(0));
if (lean_obj_tag(v_r_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1206_; 
v_a_1190_ = lean_ctor_get(v_r_1189_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_r_1189_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1192_ = v_r_1189_;
v_isShared_1193_ = v_isSharedCheck_1206_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v_r_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1206_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
lean_inc(v_a_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 1);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v___x_1196_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v___x_1187_, v___x_1188_, v___x_1195_);
lean_dec_ref(v___x_1195_);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1204_);
v___x_1198_ = v___x_1196_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v___x_1196_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v_a_1190_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1190_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1207_ = lean_ctor_get(v_r_1189_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v_r_1189_, 1);
v___x_1208_ = lean_box(0);
v___x_1209_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___lam__0(v___x_1187_, v___x_1188_, v___x_1208_);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1217_);
v___x_1211_ = v___x_1209_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_dec(v___x_1209_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 1);
lean_ctor_set(v___x_1211_, 0, v_a_1207_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1207_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT void l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1178_ = stack[0].m_obj;
lean_object* v_x_1179_ = stack[1].m_obj;
lean_object* v___y_1180_ = stack[2].m_obj;
lean_object* v___y_1181_ = stack[3].m_obj;
lean_object* v___y_1182_ = stack[4].m_obj;
lean_object* v___y_1183_ = stack[5].m_obj;
lean_object* v___y_1184_ = stack[6].m_obj;
lean_object* v___y_1185_ = stack[7].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_1178_, v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg___boxed(lean_object* v_h_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1228_;
}
}
lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(lean_object* v_00_u03b1_1229_, lean_object* v_h_1230_, lean_object* v_x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___redArg(v_h_1230_, v_x_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT void l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1230_ = stack[1].m_obj;
lean_object* v_x_1231_ = stack[2].m_obj;
lean_object* v___y_1232_ = stack[3].m_obj;
lean_object* v___y_1233_ = stack[4].m_obj;
lean_object* v___y_1234_ = stack[5].m_obj;
lean_object* v___y_1235_ = stack[6].m_obj;
lean_object* v___y_1236_ = stack[7].m_obj;
lean_object* v___y_1237_ = stack[8].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(lean_box(0), v_h_1230_, v_x_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
stack->m_obj
 = v_res_1240_;
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1241_, lean_object* v_h_1242_, lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2(v_00_u03b1_1241_, v_h_1242_, v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1251_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = l_ByteArray_empty;
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1252_);
return v___x_1254_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1258_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__3));
v___x_1259_ = lean_unsigned_to_nat(46u);
v___x_1260_ = lean_unsigned_to_nat(193u);
v___x_1261_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__2));
v___x_1262_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__1));
v___x_1263_ = l_mkPanicMessageWithDecl(v___x_1262_, v___x_1261_, v___x_1260_, v___x_1259_, v___x_1258_);
return v___x_1263_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(lean_object* v_x_1264_, uint8_t v_isolateStderr_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___y_1284_; 
v___x_1278_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__0);
v___x_1279_ = lean_st_mk_ref(v___x_1278_);
v___x_1280_ = lean_st_mk_ref(v___x_1278_);
v___x_1281_ = l_IO_FS_Stream_ofBuffer(v___x_1279_);
lean_inc(v___x_1280_);
v___x_1282_ = l_IO_FS_Stream_ofBuffer(v___x_1280_);
if (v_isolateStderr_1265_ == 0)
{
v___y_1284_ = v_x_1264_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1302_; 
lean_inc_ref(v___x_1282_);
v___x_1302_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__5___boxed), 10, 3);
lean_closure_set(v___x_1302_, 0, lean_box(0));
lean_closure_set(v___x_1302_, 1, v___x_1282_);
lean_closure_set(v___x_1302_, 2, v_x_1264_);
v___y_1284_ = v___x_1302_;
goto v___jp_1283_;
}
v___jp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1275_);
lean_ctor_set(v___x_1276_, 1, v___y_1274_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__2___boxed), 10, 3);
lean_closure_set(v___x_1285_, 0, lean_box(0));
lean_closure_set(v___x_1285_, 1, v___x_1282_);
lean_closure_set(v___x_1285_, 2, v___y_1284_);
v___x_1286_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v___x_1281_, v___x_1285_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v_data_1289_; uint8_t v___x_1290_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_st_ref_get(v___x_1280_);
lean_dec(v___x_1280_);
v_data_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref(v_data_1289_);
lean_dec(v___x_1288_);
v___x_1290_ = lean_string_validate_utf8(v_data_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v_data_1289_);
v___x_1291_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___closed__4);
v___x_1292_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__4(v___x_1291_);
v___y_1274_ = v_a_1287_;
v___y_1275_ = v___x_1292_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_string_from_utf8_unchecked(v_data_1289_);
v___y_1274_ = v_a_1287_;
v___y_1275_ = v___x_1293_;
goto v___jp_1273_;
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___x_1280_);
v_a_1294_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1286_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1286_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1264_ = stack[0].m_obj;
uint8_t v_isolateStderr_1265_ = stack[1].m_num;
lean_object* v___y_1266_ = stack[2].m_obj;
lean_object* v___y_1267_ = stack[3].m_obj;
lean_object* v___y_1268_ = stack[4].m_obj;
lean_object* v___y_1269_ = stack[5].m_obj;
lean_object* v___y_1270_ = stack[6].m_obj;
lean_object* v___y_1271_ = stack[7].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_1264_, v_isolateStderr_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg___boxed(lean_object* v_x_1304_, lean_object* v_isolateStderr_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_isolateStderr_boxed_1313_; lean_object* v_res_1314_; 
v_isolateStderr_boxed_1313_ = lean_unbox(v_isolateStderr_1305_);
v_res_1314_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_1304_, v_isolateStderr_boxed_1313_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1314_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = l_Lean_Level_succ___override(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__4);
v___x_1325_ = l_Lean_mkSort(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__5);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(lean_object* v_stx_1339_, lean_object* v_expectedType_x3f_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1));
lean_inc(v_stx_1339_);
v___x_1349_ = l_Lean_Syntax_isOfKind(v_stx_1339_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_expectedType_x3f_1340_);
lean_dec(v_stx_1339_);
v___x_1350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__0___redArg();
return v___x_1350_;
}
else
{
lean_object* v_toCold_1351_; lean_object* v_currRecDepth_1352_; lean_object* v_ref_1353_; uint16_t v_optionFlags_1354_; uint8_t v_suppressElabErrors_1355_; uint8_t v_isRecordingDeps_1356_; lean_object* v___x_1357_; lean_object* v_tk_1358_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v_ref_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_toCold_1351_ = lean_ctor_get(v_a_1345_, 0);
v_currRecDepth_1352_ = lean_ctor_get(v_a_1345_, 1);
v_ref_1353_ = lean_ctor_get(v_a_1345_, 2);
v_optionFlags_1354_ = lean_ctor_get_uint16(v_a_1345_, sizeof(void*)*3);
v_suppressElabErrors_1355_ = lean_ctor_get_uint8(v_a_1345_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1356_ = lean_ctor_get_uint8(v_a_1345_, sizeof(void*)*3 + 3);
v___x_1357_ = lean_unsigned_to_nat(0u);
v_tk_1358_ = l_Lean_Syntax_getArg(v_stx_1339_, v___x_1357_);
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = l_Lean_Syntax_getArg(v_stx_1339_, v___x_1386_);
lean_dec(v_stx_1339_);
v___x_1388_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__6);
v___x_1389_ = 0;
v___x_1390_ = lean_box(0);
v_ref_1391_ = l_Lean_replaceRef(v___x_1387_, v_ref_1353_);
lean_inc(v_ref_1391_);
lean_inc(v_currRecDepth_1352_);
lean_inc_ref(v_toCold_1351_);
v___x_1392_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1392_, 0, v_toCold_1351_);
lean_ctor_set(v___x_1392_, 1, v_currRecDepth_1352_);
lean_ctor_set(v___x_1392_, 2, v_ref_1391_);
lean_ctor_set_uint16(v___x_1392_, sizeof(void*)*3, v_optionFlags_1354_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*3 + 2, v_suppressElabErrors_1355_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*3 + 3, v_isRecordingDeps_1356_);
v___x_1393_ = l_Lean_Meta_mkFreshExprMVar(v___x_1388_, v___x_1389_, v___x_1390_, v_a_1343_, v_a_1344_, v___x_1392_, v_a_1346_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1513_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1513_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1513_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1457_; 
v___x_1398_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__2);
if (lean_obj_tag(v_expectedType_x3f_1340_) == 0)
{
v___y_1457_ = v_a_1394_;
goto v___jp_1456_;
}
else
{
lean_object* v_val_1512_; 
lean_dec(v_a_1394_);
v_val_1512_ = lean_ctor_get(v_expectedType_x3f_1340_, 0);
lean_inc(v_val_1512_);
lean_dec_ref_known(v_expectedType_x3f_1340_, 1);
v___y_1457_ = v_val_1512_;
goto v___jp_1456_;
}
v___jp_1399_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__8));
v___x_1408_ = lean_mk_empty_array_with_capacity(v___x_1386_);
v___x_1409_ = lean_array_push(v___x_1408_, v___y_1400_);
v___x_1410_ = l_Lean_Meta_mkAppM(v___x_1407_, v___x_1409_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1455_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1455_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1455_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_obj_once(&l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7, &l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7_once, _init_l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_unsafe__1___closed__7);
v___x_1416_ = 1;
v___x_1417_ = l_Lean_Meta_evalExpr___redArg(v___x_1415_, v_a_1411_, v___x_1416_, v___x_1349_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___f_1419_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1419_, 0, v_a_1418_);
v___x_1420_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v___f_1419_, v___x_1349_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v_fst_1422_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_fst_1422_);
v_snd_1423_ = lean_ctor_get(v_a_1421_, 1);
lean_inc(v_snd_1423_);
lean_dec(v_a_1421_);
v___x_1424_ = lean_string_utf8_byte_size(v_fst_1422_);
v___x_1425_ = lean_nat_dec_eq(v___x_1424_, v___x_1357_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1427_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 3);
lean_ctor_set(v___x_1413_, 0, v_fst_1422_);
v___x_1427_ = v___x_1413_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_fst_1422_);
v___x_1427_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = l_Lean_MessageData_ofFormat(v___x_1427_);
v___x_1429_ = l_Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4(v_tk_1358_, v___x_1428_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref_known(v___x_1429_, 1);
v___y_1360_ = v_snd_1423_;
v___y_1361_ = v___y_1401_;
v___y_1362_ = v___y_1402_;
v___y_1363_ = v___y_1403_;
v___y_1364_ = v___y_1404_;
v___y_1365_ = v___y_1405_;
v___y_1366_ = v___y_1406_;
goto v___jp_1359_;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_snd_1423_);
lean_dec_ref(v___y_1405_);
lean_dec(v_tk_1358_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_dec(v_fst_1422_);
lean_del_object(v___x_1413_);
v___y_1360_ = v_snd_1423_;
v___y_1361_ = v___y_1401_;
v___y_1362_ = v___y_1402_;
v___y_1363_ = v___y_1403_;
v___y_1364_ = v___y_1404_;
v___y_1365_ = v___y_1405_;
v___y_1366_ = v___y_1406_;
goto v___jp_1359_;
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1413_);
lean_dec_ref(v___y_1405_);
lean_dec(v_tk_1358_);
v_a_1439_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1420_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1420_);
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
lean_del_object(v___x_1413_);
lean_dec_ref(v___y_1405_);
lean_dec(v_tk_1358_);
v_a_1447_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1417_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1417_);
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
else
{
lean_dec_ref(v___y_1405_);
lean_dec(v_tk_1358_);
return v___x_1410_;
}
}
v___jp_1456_:
{
lean_object* v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1458_ = l_Lean_Expr_app___override(v___x_1398_, v___y_1457_);
v___x_1459_ = 0;
v___x_1460_ = l_Lean_SourceInfo_fromRef(v_ref_1391_, v___x_1459_);
lean_dec(v_ref_1391_);
v___x_1461_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__9));
v___x_1462_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__10));
lean_inc(v___x_1460_);
v___x_1463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1460_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
v___x_1464_ = l_Lean_Syntax_node2(v___x_1460_, v___x_1462_, v___x_1463_, v___x_1387_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 1);
lean_ctor_set(v___x_1396_, 0, v___x_1458_);
v___x_1466_ = v___x_1396_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1458_);
v___x_1466_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1464_, v___x_1466_, v___x_1349_, v___x_1349_, v___x_1467_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v___x_1392_, v_a_1346_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1459_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v___x_1392_, v_a_1346_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; lean_object* v_a_1472_; lean_object* v___x_1473_; 
lean_dec_ref_known(v___x_1470_, 1);
v___x_1471_ = l_Lean_instantiateMVars___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__1___redArg(v_a_1469_, v_a_1344_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc_n(v_a_1472_, 2);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l_Lean_Meta_getMVars(v_a_1472_, v_a_1343_, v_a_1344_, v___x_1392_, v_a_1346_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1474_, v___x_1467_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v___x_1392_, v_a_1346_);
lean_dec(v_a_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; uint8_t v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = lean_unbox(v_a_1476_);
lean_dec(v_a_1476_);
if (v___x_1477_ == 0)
{
v___y_1400_ = v_a_1472_;
v___y_1401_ = v_a_1341_;
v___y_1402_ = v_a_1342_;
v___y_1403_ = v_a_1343_;
v___y_1404_ = v_a_1344_;
v___y_1405_ = v___x_1392_;
v___y_1406_ = v_a_1346_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1472_);
lean_dec_ref_known(v___x_1392_, 3);
lean_dec(v_tk_1358_);
v___x_1478_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__5___redArg();
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1472_);
lean_dec_ref_known(v___x_1392_, 3);
lean_dec(v_tk_1358_);
v_a_1487_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1475_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1475_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_a_1472_);
lean_dec_ref_known(v___x_1392_, 3);
lean_dec(v_tk_1358_);
v_a_1495_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1473_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1473_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1469_);
lean_dec_ref_known(v___x_1392_, 3);
lean_dec(v_tk_1358_);
v_a_1503_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1470_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1470_);
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
else
{
lean_dec_ref_known(v___x_1392_, 3);
lean_dec(v_tk_1358_);
return v___x_1468_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_1392_, 3);
lean_dec(v_ref_1391_);
lean_dec(v___x_1387_);
lean_dec(v_tk_1358_);
lean_dec(v_expectedType_x3f_1340_);
return v___x_1393_;
}
v___jp_1359_:
{
if (lean_obj_tag(v___y_1360_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
v_a_1367_ = lean_ctor_get(v___y_1360_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___y_1360_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1369_ = v___y_1360_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___y_1360_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_io_error_to_string(v_a_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 3);
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = l_Lean_MessageData_ofFormat(v___x_1373_);
v___x_1375_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_tk_1358_, v___x_1374_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_tk_1358_);
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___y_1365_);
lean_dec(v_tk_1358_);
v_a_1378_ = lean_ctor_get(v___y_1360_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___y_1360_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___y_1360_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___y_1360_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 0);
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1339_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_1340_ = stack[1].m_obj;
lean_object* v_a_1341_ = stack[2].m_obj;
lean_object* v_a_1342_ = stack[3].m_obj;
lean_object* v_a_1343_ = stack[4].m_obj;
lean_object* v_a_1344_ = stack[5].m_obj;
lean_object* v_a_1345_ = stack[6].m_obj;
lean_object* v_a_1346_ = stack[7].m_obj;
lean_object* v_res_1514_;
v_res_1514_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(v_stx_1339_, v_expectedType_x3f_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
stack->m_obj
 = v_res_1514_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed(lean_object* v_stx_1515_, lean_object* v_expectedType_x3f_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO(v_stx_1515_, v_expectedType_x3f_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
return v_res_1524_;
}
}
lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(lean_object* v_00_u03b1_1525_, lean_object* v_h_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___redArg(v_h_1526_, v_x_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1526_ = stack[1].m_obj;
lean_object* v_x_1527_ = stack[2].m_obj;
lean_object* v___y_1528_ = stack[3].m_obj;
lean_object* v___y_1529_ = stack[4].m_obj;
lean_object* v___y_1530_ = stack[5].m_obj;
lean_object* v___y_1531_ = stack[6].m_obj;
lean_object* v___y_1532_ = stack[7].m_obj;
lean_object* v___y_1533_ = stack[8].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(lean_box(0), v_h_1526_, v_x_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_h_1538_, lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_spec__3(v_00_u03b1_1537_, v_h_1538_, v_x_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1547_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(lean_object* v_00_u03b1_1548_, lean_object* v_x_1549_, uint8_t v_isolateStderr_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___redArg(v_x_1549_, v_isolateStderr_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1549_ = stack[1].m_obj;
uint8_t v_isolateStderr_1550_ = stack[2].m_num;
lean_object* v___y_1551_ = stack[3].m_obj;
lean_object* v___y_1552_ = stack[4].m_obj;
lean_object* v___y_1553_ = stack[5].m_obj;
lean_object* v___y_1554_ = stack[6].m_obj;
lean_object* v___y_1555_ = stack[7].m_obj;
lean_object* v___y_1556_ = stack[8].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(lean_box(0), v_x_1549_, v_isolateStderr_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_x_1561_, lean_object* v_isolateStderr_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_isolateStderr_boxed_1570_; lean_object* v_res_1571_; 
v_isolateStderr_boxed_1570_ = lean_unbox(v_isolateStderr_1562_);
v_res_1571_ = l_IO_FS_withIsolatedStreams___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__2(v_00_u03b1_1560_, v_x_1561_, v_isolateStderr_boxed_1570_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1571_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(lean_object* v_00_u03b1_1572_, lean_object* v_ref_1573_, lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___redArg(v_ref_1573_, v_msg_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1573_ = stack[1].m_obj;
lean_object* v_msg_1574_ = stack[2].m_obj;
lean_object* v___y_1575_ = stack[3].m_obj;
lean_object* v___y_1576_ = stack[4].m_obj;
lean_object* v___y_1577_ = stack[5].m_obj;
lean_object* v___y_1578_ = stack[6].m_obj;
lean_object* v___y_1579_ = stack[7].m_obj;
lean_object* v___y_1580_ = stack[8].m_obj;
lean_object* v_res_1583_;
v_res_1583_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(lean_box(0), v_ref_1573_, v_msg_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
stack->m_obj
 = v_res_1583_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3___boxed(lean_object* v_00_u03b1_1584_, lean_object* v_ref_1585_, lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3(v_00_u03b1_1584_, v_ref_1585_, v_msg_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v_ref_1585_);
return v_res_1594_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(lean_object* v_00_u03b1_1595_, lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___redArg(v_msg_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1596_ = stack[1].m_obj;
lean_object* v___y_1597_ = stack[2].m_obj;
lean_object* v___y_1598_ = stack[3].m_obj;
lean_object* v___y_1599_ = stack[4].m_obj;
lean_object* v___y_1600_ = stack[5].m_obj;
lean_object* v___y_1601_ = stack[6].m_obj;
lean_object* v___y_1602_ = stack[7].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(lean_box(0), v_msg_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1606_, lean_object* v_msg_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7(v_00_u03b1_1606_, v_msg_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1615_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(lean_object* v_ref_1616_, lean_object* v_msgData_1617_, uint8_t v_severity_1618_, uint8_t v_isSilent_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___redArg(v_ref_1616_, v_msgData_1617_, v_severity_1618_, v_isSilent_1619_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1616_ = stack[0].m_obj;
lean_object* v_msgData_1617_ = stack[1].m_obj;
uint8_t v_severity_1618_ = stack[2].m_num;
uint8_t v_isSilent_1619_ = stack[3].m_num;
lean_object* v___y_1620_ = stack[4].m_obj;
lean_object* v___y_1621_ = stack[5].m_obj;
lean_object* v___y_1622_ = stack[6].m_obj;
lean_object* v___y_1623_ = stack[7].m_obj;
lean_object* v___y_1624_ = stack[8].m_obj;
lean_object* v___y_1625_ = stack[9].m_obj;
lean_object* v_res_1628_;
v_res_1628_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(v_ref_1616_, v_msgData_1617_, v_severity_1618_, v_isSilent_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
stack->m_obj
 = v_res_1628_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9___boxed(lean_object* v_ref_1629_, lean_object* v_msgData_1630_, lean_object* v_severity_1631_, lean_object* v_isSilent_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v_severity_boxed_1640_; uint8_t v_isSilent_boxed_1641_; lean_object* v_res_1642_; 
v_severity_boxed_1640_ = lean_unbox(v_severity_1631_);
v_isSilent_boxed_1641_ = lean_unbox(v_isSilent_1632_);
v_res_1642_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__4_spec__9(v_ref_1629_, v_msgData_1630_, v_severity_boxed_1640_, v_isSilent_boxed_1641_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v_ref_1629_);
return v_res_1642_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(lean_object* v_msgData_1643_, lean_object* v_macroStack_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___redArg(v_msgData_1643_, v_macroStack_1644_, v___y_1649_);
return v___x_1652_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1643_ = stack[0].m_obj;
lean_object* v_macroStack_1644_ = stack[1].m_obj;
lean_object* v___y_1645_ = stack[2].m_obj;
lean_object* v___y_1646_ = stack[3].m_obj;
lean_object* v___y_1647_ = stack[4].m_obj;
lean_object* v___y_1648_ = stack[5].m_obj;
lean_object* v___y_1649_ = stack[6].m_obj;
lean_object* v___y_1650_ = stack[7].m_obj;
lean_object* v_res_1653_;
v_res_1653_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(v_msgData_1643_, v_macroStack_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
stack->m_obj
 = v_res_1653_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10___boxed(lean_object* v_msgData_1654_, lean_object* v_macroStack_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO_spec__3_spec__7_spec__10(v_msgData_1654_, v_macroStack_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1663_;
}
}
lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1(){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1670_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___closed__1));
v___x_1671_ = ((lean_object*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___closed__1));
v___x_1672_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___boxed), 9, 0);
v___x_1673_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1669_, v___x_1670_, v___x_1671_, v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1674_;
v_res_1674_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
stack->m_obj
 = v_res_1674_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1___boxed(lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO___regBuiltin___private_Lake_DSL_Meta_0__Lake_DSL_elabRunIO__1();
return v_res_1676_;
}
}
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
